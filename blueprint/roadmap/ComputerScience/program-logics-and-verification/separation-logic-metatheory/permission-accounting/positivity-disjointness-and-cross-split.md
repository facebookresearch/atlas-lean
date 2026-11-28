# Positivity, disjointness and cross-split

Positivity forbids two non-units from joining to the unit, disjointness forbids a non-unit from joining with itself, and cross-split refines two splittings of one element into four pieces. Fractional and counting shares are positive but not disjoint, so the axioms separate the classical share models.

Present a [separation algebra](../abstract-separation-logic/separation-algebras.md) as a set $A$ with a join relation $x \oplus y = z$ that is functional, cancellative ($x_1 \oplus y = z$ and $x_2 \oplus y = z$ imply $x_1 = x_2$), commutative, associative (if $x \oplus y = a$ and $a \oplus z = b$, there is $c$ with $y \oplus z = c$ and $x \oplus c = b$) and has a unit $u$ with $u \oplus x = x$ for all $x$; the unit is unique and is the only element with $u \oplus u = u$. Write $a \preceq b$ when $a \oplus x = b$ for some $x$. The source states the properties below for a relaxed notion of separation algebra with possibly several units; single-unit algebras are a special case, in which every fact below still holds.

- *Positivity*: $a \oplus b = c$ and $c \oplus c = c$ imply $a = b = c$; two elements joining to the unit are the unit.
- *Disjointness*: $a \oplus a = b$ implies $a = b$; an element joining with itself is the unit.
- *Cross-split*: if $a \oplus b = z$ and $c \oplus d = z$, there are $ac, ad, bc, bd$ with $ac \oplus ad = a$, $bc \oplus bd = b$, $ac \oplus bc = c$ and $ad \oplus bd = d$.
- *Infinite splittability*: there is a function $\mathrm{split}$ with $\mathrm{split}\,x = (x_1, x_2)$ implying $x_1 \oplus x_2 = x$, and implying $x \oplus x = x$ whenever $x_1 \oplus x_1 = x_1$ or $x_2 \oplus x_2 = x_2$; a non-unit splits into two non-units.

The relation $\preceq$ is a preorder, and it is antisymmetric exactly when the algebra is positive. Disjointness implies positivity, but not conversely: $(\mathbb{N}, +, 0)$ is positive and every $i > 0$ violates disjointness. Addition modulo $3$ on $\{0, 1, 2\}$ is a separation algebra that is not positive, since $1 + 2 = 0$.

Share models: fractional shares are positive and infinitely splittable, with $\mathrm{split}\,s = (s/2, s/2)$, but not disjoint, as $\tfrac12 \oplus \tfrac12 = 1$; counting shares are positive but not disjoint, as $(-1) \oplus (-1) = -2$; the named shares $(\mathcal{P}(\mathbb{N}), \uplus)$, disjoint union of sets of natural numbers, are disjoint and have cross-splits by intersection but are not infinitely splittable, a singleton having no split into two nonempty sets; and restricting named shares to the infinite subsets of $\mathbb{N}$ together with $\emptyset$ restores splittability, by alternating elements, but loses cross-split, since splitting $\mathbb{N}$ into primes and non-primes and into evens and odds would need the finite share $\{2\}$.

## Depends on

- [Separation algebras](../abstract-separation-logic/separation-algebras.md)
- [Fractional and counting permission models](fractional-and-counting-permission-models.md)

## Proof depends on

None.

## Expansion

Disjointness implies positivity: from $a \oplus b = c$ and $c \oplus c = c$, rearranging $(a \oplus b) \oplus (a \oplus b) = a \oplus b$ gives $(a \oplus a) \oplus (b \oplus b) = a \oplus b$; disjointness makes $a \oplus a = a$ and $b \oplus b$ units, so cancellation gives that $a$ is the unit. Antisymmetry: if $a \oplus x = b$ and $b \oplus y = a$ then $a \oplus (x \oplus y) = a = a \oplus u$, so $x \oplus y = u$ by cancellation and positivity makes $x = y = u$; conversely, in an antisymmetric algebra $a \oplus b = u$ gives $a \preceq u \preceq a$. Without positivity the frame rule misbehaves: an empty permission could split into a write permission and an anti-permission, and framing out the anti-permission would let a program holding no resource write. Missing prerequisite: none; the share models are those of [fractional and counting permission models](fractional-and-counting-permission-models.md) and [binary tree share model](binary-tree-share-model.md).

## Sources

- R. Dockins, A. Hobor and A. W. Appel, "A fresh look at separation algebras and share accounting", *Programming Languages and Systems (APLAS 2009)*, LNCS 5904, Springer, 2009, pp. 161–177, <https://doi.org/10.1007/978-3-642-10672-9_13>, author copy dated June 2009 <https://www.cs.princeton.edu/~appel/papers/fresh-sa.pdf>, Section 2, axioms (5)–(9); Section 5, the addition-modulo-3 example, axioms (22)–(25), (29) and (30)–(32), the order (24) and the proof sketch that disjointness implies positivity; Section 6, Definitions 8–10 and the discussion of infinite subsets of $\mathbb{N}$ after Definition 10 (definition and equation numbers of the author copy).
