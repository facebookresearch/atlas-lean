# Sampled-suffix-array locate

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined, and let a
sampling assign stored values to some rows. Sampled locate of row $r$ is the $|L|$-step locate from
row $r$: following the LF-mapping from $r$, it returns the stored value of the first sampled row
reached plus the number of LF steps taken, making at most $|L|$ steps. This is the
sampled-suffix-array locate of Ferragina and Manzini (2000).
