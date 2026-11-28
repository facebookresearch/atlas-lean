# Equality of refined covers of vector addition systems is undecidable

The refined cover of a vector addition system is the downward closure of its reachability set for the ordering that keeps the first component fixed. Even for ordinary vector addition systems, whether two refined covers are equal is undecidable, although each refined cover is a recursive set.

**Setting (Bonnet, Finkel, Leroux and Zeitoun).** A *vector addition system* (VAS) of dimension $d$ is $\mathcal{V} = \langle A, \delta, \vec{x}_{\mathrm{init}} \rangle$ with a finite set $A$ of actions, a displacement $\delta(a) \in \mathbb{Z}^d$ for each action and an initial vector $\vec{x}_{\mathrm{init}} \in \mathbb{N}^d$; an action $a$ leads from $\vec{x}$ to $\vec{x} + \delta(a)$ provided the result lies in $\mathbb{N}^d$, and $\mathrm{Post}^*(\mathcal{V})$ is the set of vectors reachable from $\vec{x}_{\mathrm{init}}$. For vectors $\vec{x}, \vec{y}$ write $\vec{x} \le_{\{1\}} \vec{y}$ if $\vec{x}(1) = \vec{y}(1)$ and $\vec{x}(i) \le \vec{y}(i)$ for $2 \le i \le d$. The *refined cover* of $\mathcal{V}$ is

$$
\mathrm{Cover}_{\le_{\{1\}}}(\mathcal{V}) = \{ \vec{x} : \vec{x} \le_{\{1\}} \vec{y} \text{ for some } \vec{y} \in \mathrm{Post}^*(\mathcal{V}) \}.
$$

**Theorem (Bonnet, Finkel, Leroux and Zeitoun).** It is undecidable, given two VAS $\mathcal{V}_1$ and $\mathcal{V}_2$ of the same dimension, whether $\mathrm{Cover}_{\le_{\{1\}}}(\mathcal{V}_1) = \mathrm{Cover}_{\le_{\{1\}}}(\mathcal{V}_2)$.

The refined cover is a natural tool for VAS with one zero test on the first component, whose transition relation is monotone for $\le_{\{1\}}$. Because of this theorem, the authors compute the cover of such systems through a different notion, the filtered cover, and derive decision procedures for place-boundedness and for model checking labeled VASS with one zero test against ω-regular properties of their transition-label traces, LTL included (Theorem 7.3); the latter proof also uses control-state reachability and the reachability algorithm.

## Depends on

- [Vector addition systems](../../../vector-addition-systems.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Equality of reachability sets of Petri nets is undecidable](marking-equivalence-is-undecidable.md)

## Expansion

The proof reduces equality of reachability sets of VAS (Hack). A VAS $\mathcal{V}$ of dimension $d$ is turned into $\mathcal{V}'$ of dimension $d + 1$ whose new first component records the sum of the other components: its initial vector is $(\sum_i \vec{x}_{\mathrm{init}}(i), \vec{x}_{\mathrm{init}})$ and each action adds $\sum_i \delta(a)(i)$ to the first component. Then $(n, \vec{x})$ is reachable in $\mathcal{V}'$ exactly when $\vec{x}$ is reachable in $\mathcal{V}$ and $n = \sum_i \vec{x}(i)$. Since the first component of a vector below $(n, \vec{x})$ equals $n$, the refined cover of $\mathcal{V}'$ determines the reachability set of $\mathcal{V}$, and $\mathrm{Post}^*(\mathcal{V}_1) = \mathrm{Post}^*(\mathcal{V}_2)$ exactly when the refined covers of $\mathcal{V}_1'$ and $\mathcal{V}_2'$ are equal.

## Sources

- Rémi Bonnet, Alain Finkel, Jérôme Leroux and Marc Zeitoun, *Model Checking Vector Addition Systems with one zero-test*, Logical Methods in Computer Science 8(2), 2012, https://doi.org/10.2168/LMCS-8(2:11)2012; the definition of refined covers and the undecidability theorem for their equality, read in arXiv:1205.4458v2. Locators in arXiv:1205.4458v2: Theorem 5.1.
