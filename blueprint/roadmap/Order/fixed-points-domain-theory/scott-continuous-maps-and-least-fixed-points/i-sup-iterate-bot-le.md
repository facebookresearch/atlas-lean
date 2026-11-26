# Kleene's fixed point is the least prefixed point

Let $D$ be a pointed directed-complete partial order and $f : D \to D$ a Scott-continuous map. If $f(a) \le a$, then $\bigsqcup_n f^n(\bot) \le a$. So $\bigsqcup_n f^n(\bot)$ is the least fixed point of $f$, and even its least prefixed point (S. Abramsky and A. Jung, *Domain Theory*, Handbook of Logic in Computer Science vol. 3 (1994), Theorem 2.1.19 (1), which states leastness among fixed points; the proof gives it for prefixed points).

## Background

- [Kleene's fixed-point theorem for pointed dcpos](map-i-sup-iterate-bot.md): the supremum of the iterates is a fixed point.
- [The least fixed point lies below every prefixed point](lfp-le.md): the same statement for ω-continuous maps on ω-complete partial orders.
- [Kleene's supremum for dcpos is the least fixed point of the ω-chain construction](i-sup-iterate-bot-eq-lfp.md): the equation from which this theorem is derived.

## Sources

- S. Abramsky and A. Jung, *Domain Theory*, in *Handbook of Logic in Computer Science*, vol. 3, Clarendon Press, Oxford, 1994. Read in the authors' corrected and expanded online version, which keeps the Handbook's numbering: <https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf>.
