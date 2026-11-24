# Lace decomposition

A lace is a sequence of natural numbers of the form $(p)$ or
$(p, p, p+1, \dots, p+\ell-2)$ for some natural number $p$ and some length $\ell \ge 2$. The lace
decomposition of a finite sequence $(a_1, \dots, a_k)$ of natural numbers is its partition into
blocks of consecutive entries built greedily from left to right: starting with no blocks, each
entry $a_i$ in turn is appended to the last block if the result is again a lace, and otherwise
starts a new block $(a_i)$.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Section 3 (definitions of a lace and of the lace decomposition).
