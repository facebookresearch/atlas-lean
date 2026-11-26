# Edge cover numbers of the triangle join

For the [triangle join](triangle.md) $R[A,B]\bowtie S[B,C]\bowtie T[C,A]$, the integral edge cover number is $2$ and the fractional edge cover number is $3/2$.

The two relations $R,S$ cover all three attributes; each single relation misses one. For the fractional problem, the three constraints are $x_R+x_T\geq1$ at $A$, $x_R+x_S\geq1$ at $B$ and $x_S+x_T\geq1$ at $C$. Adding them gives $2(x_R+x_S+x_T)\geq3$. The assignment $x_R=x_S=x_T=1/2$ meets all three constraints with equality and attains the lower bound.

## Sources

- A. Atserias, M. Grohe and D. Marx, *Size Bounds and Query Plans for Relational Joins*, SIAM J. Comput. 42(4) (2013), 1737–1767, §1 (triangle example and fractional covers); revised manuscript, 29 June 2013, pp. 2–3.
