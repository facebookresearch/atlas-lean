# The pointwise directed supremum of Scott-continuous maps is Scott-continuous

Let $\alpha$ be a preorder and $\beta$ a pointed directed-complete partial order. If $F$ is a directed set of Scott-continuous maps $\alpha \to \beta$, for the pointwise order, then the pointwise supremum

$$x \mapsto \bigsqcup_{f \in F} f(x)$$

is Scott-continuous (S. Abramsky and A. Jung, *Domain Theory*, Handbook of Logic in Computer Science vol. 3 (1994), Proposition 2.1.18). Here Scott-continuous means preserving suprema of nonempty directed sets.

Abramsky and Jung state the result for dcpos $\alpha$ and $\beta$. Here $\alpha$ may be any preorder, which is more general, and $\beta$ must have a least element, which is less general.

## Background

- [Directed suprema of Scott-continuous maps are computed pointwise](is-lub-s-sup-image-of-directed-on.md): the pointwise supremum is the least upper bound, so the continuous maps form a dcpo.
- [Arbitrary pointwise suprema of Scott-continuous maps between complete lattices](scott-continuous-s-sup.md): the version for arbitrary families between complete lattices.

## Sources

- S. Abramsky and A. Jung, *Domain Theory*, in *Handbook of Logic in Computer Science*, vol. 3, Clarendon Press, Oxford, 1994. Read in the authors' corrected and expanded online version, which keeps the Handbook's numbering: <https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf>.
