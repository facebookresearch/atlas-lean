# Chase variants and their termination classes

The standard, oblivious, semi-oblivious and core chase differ in which triggers of a set of tuple-generating dependencies they apply. Each variant defines classes of dependency sets whose chase terminates on all instances along every sequence or along some sequence; the core chase is defined here, the other variants on their own pages.

**Setting.** An instance is a finite set of atoms over constants and labeled nulls. A homomorphism between instances is a map on their domains that is the identity on constants, extended to atoms; an endomorphism of $I$ is a homomorphism from $I$ to $I$ (Section 2 of the source). For a finite set $\Sigma$ of tuple-generating dependencies (tgds) $\alpha(\bar{x}, \bar{y}) \to \exists \bar{z}\, \beta(\bar{x}, \bar{z})$, a *trigger* on an instance $I$ is a pair $(\xi, h)$ of a tgd $\xi = \alpha \to \beta \in \Sigma$ and a homomorphism $h$ with $h(\alpha) \subseteq I$; it is *active* if no extension $h'$ of $h$ has $h'(\beta) \subseteq I$. *Firing* it adds $h'(\beta)$ for the extension $h'$ that maps $\bar{z}$ to fresh nulls.

**Variants.**

- The *standard chase* fires one active trigger per step, chosen nondeterministically, subject to fairness: it is the [restricted chase](restricted-chase-sequences.md), where fairness is defined.
- The *oblivious* and *semi-oblivious chase* fire every trigger, respectively one trigger for each match of the frontier, active or not; they are defined on [oblivious and semi-oblivious chase termination](oblivious-and-semi-oblivious-chase.md), and their result does not depend on the order of steps.
- **Definition (core chase).** A *core chase step* from $I$ fires all active triggers of $I$ in parallel, each with its own fresh nulls, and replaces the resulting instance by its core. A *core chase sequence* $I_0, I_1, \dots$ applies core chase steps; it *terminates* if it reaches an instance with no active trigger. It is determined by $I_0$ up to isomorphism, so no fairness condition is needed.

**Termination classes (Grahne and Onet).** For $\star \in \{\mathsf{std}, \mathsf{obl}, \mathsf{sobl}, \mathsf{core}\}$, $\mathsf{CT}^{\star}_{\forall\forall}$ is the class of finite tgd sets $\Sigma$ such that, for every instance $I$, every $\star$-chase sequence with $\Sigma$ from $I$ (every fair sequence, for the standard chase) terminates, and $\mathsf{CT}^{\star}_{\forall\exists}$ the class of $\Sigma$ such that, for every instance $I$, some $\star$-chase sequence terminates.

For the oblivious, semi-oblivious and core chase both classes coincide, $\mathsf{CT}^{\mathsf{std}}_{\forall\forall} \subsetneq \mathsf{CT}^{\mathsf{std}}_{\forall\exists}$ (the order of firing can decide termination of the standard chase), and $\mathsf{CT}^{\mathsf{obl}}_{\forall\forall} \subsetneq \mathsf{CT}^{\mathsf{sobl}}_{\forall\forall}$. A subinstance $C \subseteq I$ is a *core* of $I$ if some endomorphism $h$ of $I$ has $h(I) \subseteq C$ and no endomorphism $g$ has $g(C) \subsetneq C$; all cores of $I$ are isomorphic, so one speaks of the core of $I$ (Section 2). Since homomorphisms fix constants, the core of a database without nulls is the database itself: for $\{R(a), R(b)\}$ with constants $a, b$ it is the whole instance, unlike the core of a finite structure in the sense of homomorphisms that may move every element. In the notation of Carral, Gerlach, Larroque and Thomazo, $\mathsf{CT}^{\mathsf{std}}_{\forall\forall}$ is $\mathsf{CT}^{\mathrm{rest}}_{R\,\forall}$.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Restricted chase sequences and their termination](restricted-chase-sequences.md)
- [Oblivious and semi-oblivious chase termination](oblivious-and-semi-oblivious-chase.md)

## Proof depends on

None.

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>; Section 2 (preliminaries and the chase variations) and Section 4.1 (termination classes) of arXiv:1303.6682v1 (the copy read), <https://arxiv.org/abs/1303.6682v1>.
- David Carral, Lukas Gerlach, Lucas Larroque and Michaël Thomazo, "Restricted Chase Termination: You Want More than Fairness", *Proceedings of the ACM on Management of Data* 3(2) (PODS 2025), 1–17, 2025, <https://doi.org/10.1145/3725246>; the notation correspondence in Section 3 ("Related Work") of arXiv:2505.16551v1, the version read.
