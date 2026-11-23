# Smith's remoteness function

For an impartial game $G$, the remoteness $R(p)$ of a
position $p$ of $G$ is defined by well-founded recursion along moves; the options of $p$ are the
positions reachable from $p$ in one move. If $p$ has no options, then $R(p) = 0$. Otherwise, if
some option $q$ of $p$ has $R(q)$ even, then $R(p)$ is $1$ plus the least even value of $R(q)$
over the options $q$ of $p$; if every option $q$ of $p$ has $R(q)$ odd, then $R(p)$ is $1$ plus
the largest value of $R(q)$ over the options $q$ of $p$.

## Sources

- C. A. B. Smith, *Graphs and composite games*, J. Combin. Theory 1 (1966), 51–81; as recalled in Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Section 1.3.
