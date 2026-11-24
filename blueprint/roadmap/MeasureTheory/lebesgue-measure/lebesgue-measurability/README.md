# Lebesgue measurability by approximation

Let $\mu$ be a measure on a topological space whose Borel sets are measurable, and suppose $\mu$
is outer regular and $\sigma$-finite, as Lebesgue measure on $\mathbb{R}^d$ is. Then a set $E$ is
null-measurable, that is, differs from a measurable set by a subset of a null set, if and only if
for every $\varepsilon > 0$ there is an open set $U \supseteq E$ with
$\mu(U \setminus E) \le \varepsilon$, where $\mu$ of a non-measurable set means its outer measure.
For Lebesgue measure, null-measurability is Lebesgue measurability.

## Idea

This is Littlewood's first principle, "every measurable set is nearly open". Tao takes the
approximation property as the definition of a Lebesgue measurable set; the card shows that it
agrees with the measure-theoretic definition, and also with the forms "a $G_\delta$ set minus a
null set" and "nearly contains a closed set". One direction needs no regularity: the open sets
$U_n$ with error $1/n$ intersect to a $G_\delta$ set $G \supseteq E$ with $\mu(G \setminus E) = 0$.
The converse uses outer regularity on pieces of finite measure, with errors $\varepsilon 2^{-n}$.
A Vitali set is a subset of $\mathbb{R}$ with no such approximation.

## Statements

- [Lebesgue measurability by outer approximation](null-measurable-set-iff-forall-exists-is.md)
- [Tao's definition of Lebesgue measurability implies null-measurability](null-measurable-set-of-forall-exists-is.md): one direction, with no hypothesis on $\mu$.
- [Outer approximation by open sets](exists-is-open-measure-sdiff-le.md): the other direction.
- [Inner approximation by closed sets](null-measurable-set-iff-forall-exists-is-2.md): the equivalent form with closed sets inside.
- [Measurable sets are $G_\delta$ sets up to null sets](null-measurable-set-iff-exists-is-g.md): the equivalent form with $G_\delta$ sets.
- [Subsets of a $G_\delta$ set with null difference are null-measurable](null-measurable-set-of-is-g.md): one direction of the $G_\delta$ form.
- [Open outer approximation gives a $G_\delta$ hull](exists-is-g-of-forall-exists-is-open.md): the step from open approximation to a $G_\delta$ hull.

## Sources

- T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, American Mathematical Society, 2011, Section 1.2.

## Related topics

- [Carathéodory extension theorem](../../measures/carath-odory-s-extension-theorem/caratheodory-extension-theorem.md): extending a content on an algebra of sets to a measure, which is how Lebesgue measure is built from the lengths of intervals.
