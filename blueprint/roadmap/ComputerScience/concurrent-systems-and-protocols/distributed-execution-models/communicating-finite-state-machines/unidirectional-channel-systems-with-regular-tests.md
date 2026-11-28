# Reachability for unidirectional channel systems with regular tests is undecidable

In a unidirectional channel system, a sender writes to one reliable and one lossy FIFO channel that a receiver reads. Reachability is decidable for such systems, but it becomes undecidable once the sender may test channel contents, already with parity tests or head tests on the reliable channel.

**Setting (Jančar, Karandikar and Schnoebelen).** A *unidirectional channel system with tests* (UCST) is $S = (\mathit{Ch}, M, Q_1, \Delta_1, Q_2, \Delta_2)$ with a finite message alphabet $M$, disjoint finite state sets $Q_1$ of Sender and $Q_2$ of Receiver, finite rule sets $\Delta_1, \Delta_2$, and two channels $\mathit{Ch} = \{\mathtt{r}, \mathtt{l}\}$, where $\mathtt{r}$ is reliable and $\mathtt{l}$ is lossy. A rule $(q, c, \alpha, q')$ of Sender (respectively Receiver) changes its state from $q$ to $q'$ and performs an action $\alpha$ on channel $c$: a *test* that the contents of $c$ belong to a regular language $R \subseteq M^\ast$, sending (respectively reading) a message $a \in M$, or nothing. A configuration $(q_1, q_2, u, v)$ consists of the two states and the contents $u$ of $\mathtt{r}$ and $v$ of $\mathtt{l}$; writes append at the end, reads remove from the front, and a *message loss* step deletes one occurrence of a message from $v$ at any time. *E-E-Reach* asks, given a UCST and states $p_{\mathrm{init}}, p_{\mathrm{fin}} \in Q_1$, $q_{\mathrm{init}}, q_{\mathrm{fin}} \in Q_2$, whether there is a run from $(p_{\mathrm{init}}, q_{\mathrm{init}}, \varepsilon, \varepsilon)$ to $(p_{\mathrm{fin}}, q_{\mathrm{fin}}, \varepsilon, \varepsilon)$. For a set $\mathcal{T}$ of regular languages, $\mathrm{UCST}[\mathcal{T}]$ allows only tests from $\mathcal{T}$; $\mathcal{P} = \{(MM)^\ast, M(MM)^\ast\}$ are the *parity tests* and $\mathcal{H} = \{a M^\ast : a \in M\}$ the *head tests*. $\mathrm{UCST}[\mathcal{P}^{\mathtt{r}}_1]$ and $\mathrm{UCST}[\mathcal{H}^{\mathtt{r}}_1]$ restrict these tests to Sender testing channel $\mathtt{r}$.

**Theorem (Jančar, Karandikar and Schnoebelen).** E-E-Reach is undecidable for $\mathrm{UCST}[\mathcal{P}^{\mathtt{r}}_1]$ and for $\mathrm{UCST}[\mathcal{H}^{\mathtt{r}}_1]$.

Without tests, E-E-Reach is decidable (a result of Chambart and Schnoebelen). The same paper shows that generalized reachability stays decidable with emptiness and non-emptiness tests, while recurrent reachability is $\Sigma^0_1$-complete already with emptiness tests by Sender on $\mathtt{r}$.

## Depends on

- [Lossy channel systems](lossy-channel-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The reduction simulates queue automata, finite-state machines with one reliable FIFO queue that they both write and read, which are Turing-powerful. Sender plays the queue automaton and writes to $\mathtt{r}$ itself. To read a message $a$ from $\mathtt{r}$, which Sender cannot do, it records the parity of the length of $\mathtt{r}$ with a parity test and writes the request $a$ on $\mathtt{l}$; Receiver, acting as a proxy, reads the request from $\mathtt{l}$ and then reads $a$ from $\mathtt{r}$ if it is there; Sender waits until the parity of $\mathtt{r}$ has changed and concludes that the read happened. A lost request, or a guess of a message that is not at the head of $\mathtt{r}$, only makes the protocol deadlock, so the simulation is faithful. Head tests serve the same purpose.

## Sources

- Petr Jančar, Prateek Karandikar and Philippe Schnoebelen, "On Reachability for Unidirectional Channel Systems Extended with Regular Tests", Logical Methods in Computer Science 11(2), 2015, <https://doi.org/10.2168/LMCS-11(2:2)2015>; Section 2 (UCSTs, operational semantics and reachability problems), the undecidability theorem of Section 3 ("Testing channels and the undecidability of reachability") and the recurrent reachability theorem of the section on two undecidable problems for UCST with emptiness and non-emptiness tests, read in arXiv:1406.5067v5, <https://arxiv.org/abs/1406.5067v5>.
