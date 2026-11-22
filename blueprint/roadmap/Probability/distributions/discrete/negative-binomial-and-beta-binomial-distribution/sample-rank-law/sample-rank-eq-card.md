# Count formula for the sample rank

For $r \ge 1$ and every score vector $\omega$ (ties included), the [sample rank](sample-rank.md) is

$$J(\omega) = \#\bigl\{ s : \#\{ i : \omega_i \le \tilde\omega_s \} < r \bigr\},$$

where $\omega_i$ are the real and $\tilde\omega_s$ the synthetic scores: a synthetic score lies strictly
below $S_{(r)}$ if and only if fewer than $r$ real scores are at most it.
