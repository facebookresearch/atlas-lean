# Bit-length growth of integer bucket elimination

Run bucket elimination over $\mathbb{Z}$ with domain size $d$, an elimination order of length $\ell$ and $f$ initial factors whose entries have absolute value at most $W \ge 1$. Then every intermediate table entry and the final result $z$ satisfy

$$
|z| \le d^{\ell} \cdot W^{f},
$$

so all binary encodings have length $O(\ell \log d + f \log W)$; over $\mathbb{Z}/p\mathbb{Z}$ entries stay below $p$. In particular bucket elimination runs in time polynomial in the input size and $d^{w^*}$, with no doubly exponential bit growth.

## Proof sketch

Maintain the invariant that each live factor's entries are bounded by $d$ to the number of variables eliminated into it times $W$ to the number of initial factors merged into it; summing over $d$ values and multiplying factors adds exponents.

## Depends on

- [Bucket elimination over explicit factor tables](bucket-elimination-over-factor-tables.md)

## Sources

- R. Dechter, "Bucket Elimination: A Unifying Framework for Reasoning", Artificial Intelligence 113(1-2), 1999.
- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
