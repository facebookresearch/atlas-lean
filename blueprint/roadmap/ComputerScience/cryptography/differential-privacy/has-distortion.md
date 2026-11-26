# Distortion

Answers $\tilde a_q \in \mathbb{R}$ to the subset-sum queries $q \subseteq \{0, \dots, n - 1\}$ on a database $d \in \{0,1\}^n$ have *distortion* at most $E$ if every answer is within $E$ of the exact answer: $|\tilde a_q - a_q(d)| \le E$ for every $q$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.1 (the distortion $|A(S) - r(S)|$ of a response $r(S)$, bounded by $E$ in Theorem 8.1)
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003, pp. 202–210, Definition 2 (answers within $E$ perturbation)
