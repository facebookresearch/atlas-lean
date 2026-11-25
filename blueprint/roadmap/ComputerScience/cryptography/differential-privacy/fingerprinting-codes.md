# Fingerprinting codes

For a codebook $C \in \{0,1\}^{n \times d}$ with rows $c_1, \dots, c_n$ and a coalition $S \subseteq [n]$, the set of *feasible* codewords is
$F(C_S) = \{c' \in \{0,1\}^d : \forall j \in [d]\ \exists i \in S,\ c'_j = c_{ij}\}$; a feasible word is constrained only in the columns where all members of $S$ agree.

For $n, d \in \mathbb{N}$ and $\xi \in (0, 1]$, a pair of algorithms $(\mathrm{Gen}, \mathrm{Trace})$, which may share state, is an *$(n, d)$-fingerprinting code with security $\xi$* if
$\mathrm{Gen}$ outputs a codebook $C \in \{0,1\}^{n \times d}$ and, for every possibly randomized adversary $A$ and every coalition $S \subseteq [n]$, with $c' \leftarrow A(C_S)$:

1. $\Pr[c' \in F(C_S) \wedge \mathrm{Trace}(C, c') = \bot] \le \xi$;
2. $\Pr[\mathrm{Trace}(C, c') \in [n] \setminus S] \le \xi$;

the probabilities taken over the coins of $\mathrm{Gen}$, $\mathrm{Trace}$ and $A$. Tardos's construction gives, for every $d$ and every $\xi \in (0, 1)$, an $(n, d)$-fingerprinting code with
security $\xi$ for $n = \tilde\Omega(\sqrt{d / \log(1/\xi)})$. Bun, Ullman and Vadhan use such codes to lower-bound the sample complexity of approximate
differential privacy.

## Depends on

- [Differential privacy](differentially-private.md)

## Sources

- M. Bun, J. Ullman and S. Vadhan, "Fingerprinting codes and the price of approximate differential privacy", *SIAM Journal on Computing* 47(5):1888–1938, 2018, <https://arxiv.org/abs/1311.3158>: Section 3 (feasible codewords, Definition 3.1 and Theorem 3.2).
