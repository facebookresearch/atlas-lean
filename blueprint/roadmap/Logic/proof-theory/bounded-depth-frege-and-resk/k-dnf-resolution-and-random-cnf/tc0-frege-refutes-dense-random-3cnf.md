# TC$^0$-Frege refutes dense random 3CNFs

With probability $1-o(1)$, a random 3CNF with $n$ variables and $cn^{1.4}$ clauses, for a large enough constant $c$, has polynomial-size TC$^0$-Frege refutations, while for at most $n^{1.5-\epsilon}$ clauses resolution needs exponential size, so TC$^0$-Frege is exponentially faster on such formulas.

A *random 3CNF* with $m$ clauses on $x_1,\dots,x_n$ is obtained by choosing $m$ clauses independently, with repetitions, from all $2^3\binom n3$ clauses with three literals.

**Theorem.** With probability $1-o(1)$, a random 3CNF with $n$ variables and $cn^{1.4}$ clauses, for a sufficiently large constant $c$, has polynomial-size [TC$^0$-Frege](../bounded-depth-frege-systems/tc0-frege-systems.md) refutations.

**Corollary.** With probability converging to $1$, a random 3CNF $\mathcal K$ with $n$ variables and $m\ge cn^{1.4}$ clauses, $c$ a sufficiently large constant, has polynomially bounded TC$^0$-Frege proofs of $\neg\mathcal K$, while $\mathcal K$ has no subexponential-size resolution refutations as long as $m=O(n^{1.5-\epsilon})$ for some $0<\epsilon<1/2$.

## Expansion

The refutations formalize the Feige-Kim-Ofek unsatisfiability witnesses: with probability tending to $1$, a random 3CNF with $m=cn^{1.4}$ clauses has small imbalance $I$ (the sum over variables of the difference between positive and negative occurrences), a matrix $M$ built from pairs of variables sharing a clause whose largest eigenvalue $\lambda$ is $O(n^{0.2})$, and a collection of $t$ inconsistent even $k$-tuples of clauses (every variable occurs an even number of times and the number of negations is odd) with each clause in at most $d$ tuples, where $t>d(I+\lambda n)/2+o(1)$. Counting satisfied literals, not-all-equal clauses and violated 3XOR constraints shows no assignment can exist. The authors prove this "main formula" in the bounded arithmetic theory $\mathbf{VTC}^0$, carrying out the spectral bound with rational approximations of an eigenvector basis, and translate the $\mathbf{VTC}^0$ proof into polynomial-size TC$^0$-Frege proofs. The resolution lower bound comes from Ben-Sasson and Wigderson; compare [random CNFs in resolution](../../resolution-separations-and-supercritical-tradeoffs/chvatal-szemeredi-random.md) and the [Res($k$) lower bounds](res-k-lower-bounds-for-random-cnf.md).

## Depends on

- [TC0-Frege (threshold logic)](../bounded-depth-frege-systems/tc0-frege-systems.md)

## Proof depends on

None.

## Sources

- Sebastian Müller and Iddo Tzameret, "Short propositional refutations for dense random 3CNF formulas", *Annals of Pure and Applied Logic*, 2014, https://doi.org/10.1016/j.apal.2014.08.001; numbering as in arXiv:1101.3970v2 (Definition 2.2; main theorem of Section 1.2; Definitions 4.1-4.6; Theorem 5.1; Theorem 7.2; Corollary 7.6).
