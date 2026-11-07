# The $Q$-bonacci run condition

Let $r, s \in \mathbb{N}$ and let $R$ be a list of runs,
each a pair (letter, length) with a Boolean letter. For the run at position $i$, let $v_i$ be the
length of the run at position $i + 1$ if that run exists and has letter false, and $v_i = 0$
otherwise. Then $R$ satisfies the $Q$-bonacci run condition for $q = r/s$ when every run of
letter true, say of length $p$ at position $i$, has $p \le r$ and also $p s \le r v_i$, except
that $p s \le r v_i$ may fail when both this run is the last run of letter true in $R$ and
either $p = r$ or $v_i = 0$.

Applied to the maximal runs of the block word of a Dyck path, the runs of letter true are the
blocks of $p$ consecutive $1$-peaks and $v_i$ counts the $0$-valleys that follow them: every
block but the last needs $p s \le r v_i$, and the last block, of $p_k$ peaks followed by $v_k$
valleys, needs it only when $p_k < r$ and $v_k \ne 0$.

## Sources

- Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.3.2, Definition 4.
