# Bell-Chueluecha-Warnke: sunflower bound O(r log l)^l

There is an absolute constant $C$ such that every family of more than $(C r \log \ell)^{\ell}$ sets of size $\ell \ge 2$ contains an $r$-sunflower. The Erdős-Rado conjecture asks for a bound of the form $C_r^{\ell}$.

## Proof sketch

Refine the encoding argument of the spread lemma so that the failure probability decays exponentially in the number of rounds, allowing a density $\delta = O(\log(\ell)/\kappa)$ rather than $O(\log(\ell r)/\kappa)$ while still obtaining failure probability below $1/r$ via iterating over $O(\log r)$ independent rounds whose cost is absorbed.

## Depends on

- [Sunflower](../intersecting-families/sunflower-lemma/is-sunflower.md)

## Proof depends on

- [Rao: sunflower bound via the converse of Shannon's source coding theorem](rao-sunflower-bound-via-coding.md)

## Sources

- Tolson Bell, Suchakree Chueluecha, Lutz Warnke, "Note on sunflowers", Discrete Mathematics 344(7) (2021); arXiv:2009.09327.
