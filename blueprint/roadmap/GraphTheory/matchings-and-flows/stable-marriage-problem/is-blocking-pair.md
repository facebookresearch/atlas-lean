# Blocking pair

Let $M$ and $W$ be sets. Suppose that each $m \in M$ has a strict total
order $\lt _m$ of preference on $W$ and each $w \in W$ has a strict total order $\lt _w$ of preference
on $M$, where $x \lt _m y$ means that $m$ prefers $x$ to $y$, and likewise for $\lt _w$. For a perfect
matching $\mu$ between $M$ and $W$, a pair $(m, w) \in M \times W$ is a blocking pair when
$w \lt _m \mu(m)$ and $m \lt _w \mu^{-1}(w)$, that is, when $m$ prefers $w$ to $\mu(m)$ and $w$ prefers
$m$ to $\mu^{-1}(w)$.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, §2: a matching `x` is unstable with respect to `m_k` and `w_q` when each prefers the other to the partner `x` gives it.
- D. Gale and L. S. Shapley, "College admissions and the stability of marriage", *American Mathematical Monthly* 69 (1962), 9–15, DOI 10.2307/2312726, the Definition in the college-admissions section and its marriage version ("a set of marriages unstable") in the section on the stable marriage problem.
