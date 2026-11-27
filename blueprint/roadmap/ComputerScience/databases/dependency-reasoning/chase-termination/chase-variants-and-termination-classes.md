# Chase variants and their termination classes

The standard, oblivious, semi-oblivious and core chase differ in which triggers of a set of tuple-generating dependencies they fire. Each variant defines classes of dependency sets whose chase terminates on all instances, along all branches or along some branch.

**Setting.** An instance is a finite set of atoms over constants and labeled nulls. For a finite set $\Sigma$ of tuple-generating dependencies (tgds) $\alpha(\bar{x}, \bar{y}) \to \exists \bar{z}\, \beta(\bar{x}, \bar{z})$, a *trigger* on an instance $I$ is a pair $(\xi, h)$ of a tgd $\xi = \alpha \to \beta \in \Sigma$ and a homomorphism $h$ with $h(\alpha) \subseteq I$; it is *active* if no extension $h'$ of $h$ has $h'(\beta) \subseteq I$. *Firing* it adds $h'(\beta)$ for the extension $h'$ that maps $\bar{z}$ to fresh nulls. A chase sequence $I_0, I_1, \dots$ fires one trigger per step and *terminates* if it reaches an instance with no trigger left to fire; infinite sequences are required to be fair.

**Definition (Grahne and Onet).** The variants are:

- the *standard chase*, which fires an active trigger, chosen nondeterministically;
- the *oblivious chase*, which fires any trigger, active or not, each at most once in a sequence;
- the *semi-oblivious chase*, which treats triggers $(\xi, h)$ and $(\xi, g)$ with $h(\bar{x}) = g(\bar{x})$ as equivalent and fires exactly one per equivalence class;
- the *core chase*, which at each step fires all active triggers in parallel and replaces the result by its core; it is deterministic.

For $\star \in \{\mathsf{std}, \mathsf{obl}, \mathsf{sobl}, \mathsf{core}\}$, $\mathsf{CT}^{\star}_{\forall\forall}$ is the class of finite tgd sets $\Sigma$ such that, for every instance $I$, every $\star$-chase sequence with $\Sigma$ from $I$ terminates, and $\mathsf{CT}^{\star}_{\forall\exists}$ the class of $\Sigma$ such that, for every instance $I$, some $\star$-chase sequence terminates.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Cores of finite relational structures](../../../../TheoryOfComputation/np-completeness/satisfiability/finite-domain-csp-dichotomy/cores-of-finite-relational-structures.md)

## Proof depends on

None.

## Expansion

For the oblivious and semi-oblivious chase both classes coincide, $\mathsf{CT}^{\mathsf{std}}_{\forall\forall} \subsetneq \mathsf{CT}^{\mathsf{std}}_{\forall\exists}$ (the order of firing can decide termination of the standard chase), and $\mathsf{CT}^{\mathsf{obl}}_{\forall\forall} \subsetneq \mathsf{CT}^{\mathsf{sobl}}_{\forall\forall}$. The core of an instance is a minimal retract, unique up to isomorphism. The oblivious and semi-oblivious chase for single-head dependencies are also described on [oblivious and semi-oblivious chase termination](oblivious-and-semi-oblivious-chase.md).

## Sources

- Gösta Grahne and Adrian Onet, "Anatomy of the Chase", Fundamenta Informaticae 157(3), pp. 221–270, 2018, <https://doi.org/10.3233/FI-2018-1627>; Section 2 (preliminaries and the chase variations) and Section 4.1 (termination classes) of arXiv:1303.6682v1 (the copy read), <https://arxiv.org/abs/1303.6682v1>.
