# Skorokhod EDist

The **Skorokhod J1 extended distance** between two real paths on `[0, T]`:
the infimum over increasing bijections `φ` of `[0, T]` (order isomorphisms, the J1 time
changes) of `max (sup_t |φ t - t|) (sup_t |f t - g (φ t)|)`.

## Sources

- Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), §12, eq. (12.13); the infimum over `Λ` of `‖λ - id‖ ∨ ‖x - y ∘ λ‖`. Here the comparison is written as `f t` against `g (φ t)`, which is the same quantity after replacing `φ` by its inverse.
