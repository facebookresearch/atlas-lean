# c3-locally testable code families

A family of binary linear codes $C_n \subseteq \mathbb{F}_2^{N_n}$ with $N_n \to \infty$ is a **$c^3$-LTC family** if there are constants $r, \delta, \kappa > 0$ and $q \in \mathbb{N}$ such that for every $n$:

1. (constant rate) $\dim C_n \ge r N_n$;
2. (constant distance) the minimum distance of $C_n$ is at least $\delta N_n$;
3. (constant locality) there is a tester that reads at most $q$ coordinates of a word $w \in \mathbb{F}_2^{N_n}$, always accepts codewords, and rejects every $w$ with probability at least $\kappa \cdot \operatorname{dist}(w, C_n)/N_n$.

Equivalently, $C_n$ is the kernel of a parity-check matrix whose rows have weight at most $q$ and satisfies the soundness inequality $|Hw|/m \ge \kappa \operatorname{dist}(w, C_n)/N_n$, where $m$ is the number of rows.

## Depends on

- [Locally testable code](../locally-testable-codes/ltc.md)
- [Good family of codes](../locally-testable-codes/is-good.md)
- [Rate of a binary code](../locally-testable-codes/rate.md)
- [Minimum distance of a binary code](../locally-testable-codes/distance.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- P. Panteleev, G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022), arXiv:2111.03654.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
