# Blatant non-privacy

A mechanism $M$ releases, for every $n$ and every database $d \in \{0,1\}^n$ of one sensitive bit per person, a random output $M_n(d)$, for instance its answers to all subset-sum queries on $d$. It is *blatantly non-private* if an adversary can construct from the output a candidate that agrees with the database on all but $o(n)$ entries, except with negligible probability: there are maps $A_n$ from outputs to candidates $c \in \{0,1\}^n$ such that, for every choice of databases $d_n \in \{0,1\}^n$ and every $\varepsilon > 0$, the probability that $A_n(M_n(d_n))$ differs from $d_n$ in more than $\varepsilon n$ entries (its outer probability if this event is not measurable) is $o(n^{-k})$ for every $k \in \mathbb{N}$. The adversary sees the whole output; a mechanism whose answers also depend on the history of queries enters through a chosen output, such as its answers to a fixed set of queries asked at once. The adversary may depend on $M$ but not on the database, has no bound on its running time, and need not know on which entries it is correct.

For a deterministic mechanism, whose output on each database is a single value, with outputs in a space whose points are measurable (a countable space with its discrete $\sigma$-algebra or $\mathbb{R}^m$ with its Borel $\sigma$-algebra, for instance), the condition says that $A_n(M_n(d_n))$ differs from $d_n$ in $o(n)$ entries.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.1, Definition 8.1
- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003, pp. 202–210, Definition 3 (success with probability $1 - \mathrm{neg}(n)$ for every $\varepsilon > 0$, there for adversaries of bounded running time) and Remark 1 (queries asked at once)
