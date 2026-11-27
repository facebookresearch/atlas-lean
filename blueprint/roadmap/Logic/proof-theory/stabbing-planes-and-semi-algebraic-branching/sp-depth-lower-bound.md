# Communication-based depth lower bounds for stabbing planes

Let $F$ be an unsatisfiable CNF formula on $n$ variables and $(X, Y)$ a partition of its variables. Every stabbing planes refutation of $F$ of depth $d$ yields a real communication protocol of cost $O(d + \log n)$ and a public-coin randomized bounded-error protocol of cost $O(d \log n + \log^2 n)$ for the falsified-clause search problem $\mathrm{Search}_{X,Y}(F)$. Consequently, if $\mathrm{Search}_{X,Y}(F)$ has randomized communication complexity $R$, then every stabbing planes refutation of $F$ has depth $\Omega(R/\log n) - O(\log n)$; lifted formulas whose search problems have randomized communication complexity $n^{\Omega(1)}$ require depth $n^{\Omega(1)}/\log n$.

## Proof sketch

Alice and Bob walk down the refutation tree from the root. At a node querying $a \cdot x \ge b$ they decide which child contains their joint Boolean input, which amounts to comparing $a_X \cdot x$ with $b - a_Y \cdot y$; by Muroga's bound the inequality may be taken with coefficients of $O(n \log n)$ bits, so Nisan's public-coin protocol decides it with error $\varepsilon$ in $O(\log n + \log(1/\varepsilon))$ bits, and a real protocol decides it with one bit. The walk ends at a leaf whose polytope is empty while the input satisfies every inequality on the path, so the input violates an inequality of $F$, that is, falsifies a clause. The players still have to find that clause: the leaf's Farkas certificate is a nonnegative combination of the path inequalities, the bounds $0 \le x_i \le 1$ and clause inequalities of $F$ (by Carathéodory at most $n + 1$ of the latter are needed) that yields $0 \ge 1$. The input satisfies the path inequalities and the bounds, so the combined slack of the certificate's clause inequalities on the input is negative; a binary search over halves of this clause part, each step one more linear-inequality evaluation, finds a violated clause in $O(\log n)$ steps. At most $d + O(\log n)$ inequalities are evaluated, and with $\varepsilon = \Theta(1/(d + \log n))$ per evaluation a union bound gives the randomized cost. Lower bounds for lifted search problems then follow from randomized lifting theorems.

## Depends on

- [The stabbing planes proof system](stabbing-planes-system.md)
- [Public-coin randomized protocol](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/public-coin-protocol.md)

## Proof depends on

- [Göös–Pitassi–Watson: query-to-communication lifting for BPP](../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/gpw-bpp-lifting.md)

## Sources

- P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere, "Stabbing planes", ITCS (2018), LIPIcs 94, Art. 10, doi:10.4230/LIPIcs.ITCS.2018.10, arXiv:1710.03219 (Lemma 17).
- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", CCC (2021), arXiv:2102.05019.
