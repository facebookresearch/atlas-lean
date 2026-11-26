# Leading-pair recurrence for Arndt compositions

Let $a(n,k)$ count Arndt compositions
of $n$ with $k$ parts. For all natural numbers $n,k$,

$$a(n,k+2)=\sum_{s+t=n}\left\lfloor\frac{\max(s-1,0)}2\right\rfloor a(t,k),$$

where $s,t$ range over natural numbers. For a leading descending pair of weight $s$, its
smaller part can be any integer from $1$ to $\lfloor(s-1)/2\rfloor$.

## Sources

- D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*, arXiv:2311.15388v1, proof of Theorem 2.1 (decomposition into descending pairs).
