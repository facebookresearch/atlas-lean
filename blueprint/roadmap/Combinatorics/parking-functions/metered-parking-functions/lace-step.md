# One step of the lace decomposition

Given a list of blocks (each a list of natural
numbers) and a natural number $a$: if the last block is $(p)$ with $a = p$, or the last block has
at least two entries and ends with $e$ where $a = e + 1$, then $a$ is appended to the last block;
otherwise, including when there is no block, a new block $(a)$ is added at the end.

Applied to a list of laces, where a lace is $(p)$ or $(p, p, p+1, \dots, p+\ell-2)$ for some
natural number $p$ and some length $\ell \ge 2$, this extends the last lace exactly when the
result is again a lace.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace decomposition).
