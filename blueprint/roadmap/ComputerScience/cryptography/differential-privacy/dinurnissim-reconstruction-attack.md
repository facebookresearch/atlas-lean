# Dinur–Nissim reconstruction attack

Let $d \in \{0,1\}^n$. If a mechanism answers all $2^n$ subset-sum queries with distortion at most $E$, then an adversary (running in exponential time) outputs $c \in \{0,1\}^n$ that differs from $d$ in at most $4E$ positions. If the distortion is $E = o(\sqrt n)$, then an adversary asking $O(n \log^2 n)$ uniformly random subset-sum queries and solving a linear program reconstructs $d$ up to $o(n)$ errors in polynomial time, with high probability. Consequently a mechanism that avoids blatant non-privacy against polynomial-time adversaries must add distortion $\Omega(\sqrt n)$.

## Depends on

- [Blatant non-privacy and distortion of subset-sum mechanisms](blatant-non-privacy-and-distortion-of-subset.md)

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 8.1
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003
