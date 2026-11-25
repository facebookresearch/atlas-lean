# Blatant non-privacy and distortion of subset-sum mechanisms

Let $d \in \{0,1\}^n$ be a database and, for $q \subseteq [n]$, let $a_q(d) = \sum_{i \in q} d_i$ be the subset-sum query. A mechanism answering subset-sum queries has *distortion* $E$ if every answer $\tilde a_q$ satisfies $|\tilde a_q - a_q(d)| \le E$. A mechanism is *blatantly non-private* if an adversary interacting with it outputs $c \in \{0,1\}^n$ that agrees with $d$ on all but $o(n)$ entries.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003
