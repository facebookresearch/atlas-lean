# Signature-free asynchronous binary Byzantine agreement with O(n^2) messages per round

Assume $n \ge 3t + 1$, reliable authenticated channels and a common coin. There is a signature-free asynchronous binary Byzantine agreement protocol in which correct processes send $O(n^2)$ constant-size messages per round, excluding the cost of the coin, and every correct process decides within an expected constant number of rounds; hence the expected message complexity is $O(n^2)$. This is the protocol of the journal version (JACM 2015) of Mostéfaoui, Moumen and Raynal, or the corrected version of the simpler PODC 2014 round given by Cachin and Zanolini (DISC 2021), which additionally assumes FIFO links.

## Proof sketch

In the PODC 2014 round, processes run binary-value broadcast on their estimates, then broadcast one value from $\mathrm{bin\_values}$ in an auxiliary message and wait for $n - t$ auxiliary messages whose values are contained in $\mathrm{bin\_values}$; with the collected set $B$ fixed, they release the coin $s$. If $B=\{b\}$, the process adopts $b$ and decides if $b = s$; otherwise it adopts $s$. Quorum intersection shows that at most one singleton value can be collected by correct processes in a round. In full asynchrony this single round does not guarantee termination: the adversary can reorder and delay messages between correct processes until the coin value is known and steer the collected sets accordingly (Tholoniat and Gramoli). The JACM 2015 version avoids this with a modified, extended round using more communication steps. Cachin and Zanolini keep the simple round but assume FIFO links (also for the coin's messages), let $B$ change while the coin protocol runs, and add decide messages relayed after $t + 1$ and adopted after $2t + 1$ copies; then with probability $1/2$ per round the coin matches the unique possible singleton, and all correct processes decide within expected constant rounds.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Binary-value broadcast filters values proposed only by Byzantine processes](binary-value-broadcast.md)

## Sources

- A. Mostéfaoui, H. Moumen, M. Raynal, "Signature-Free Asynchronous Binary Byzantine Consensus with t < n/3, O(n^2) Messages, and O(1) Expected Time", Journal of the ACM 62(4) (2015); PODC 2014.
- G. Bracha, "Asynchronous Byzantine Agreement Protocols", Information and Computation 75(2) (1987).
- C. Cachin, L. Zanolini, "Brief Announcement: Revisiting Signature-Free Asynchronous Byzantine Consensus", DISC 2021; full version "From Symmetric to Asymmetric Asynchronous Byzantine Consensus", arXiv:2005.08795.
- P. Tholoniat, V. Gramoli, "Formal Verification of Blockchain Byzantine Fault Tolerance", 2019.
