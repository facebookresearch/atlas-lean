# Satisfiability of probability logic with summation and free range variables is undecidable

For the logics comparing polynomials in probabilities, with summation over values and free value variables read universally, satisfiability of finite sequents is undecidable, both in purely probabilistic and in causal form and both over all models and over models with finite ranges.

**Languages (Ibeling, Icard and Mossé).** Each random variable $V$ has constant symbols $c^V_1, c^V_2, \dots$ and range variables $v_1, v_2, \dots$ standing for its values. Base formulas are Boolean combinations of atoms $V = v$ and $V = c^V_i$. Probability terms are built from conditional probabilities $\mathbf{P}(\delta \mid \delta')$ of base formulas by summation $\sum_{v_i} t$ over a range variable, sum, product, negation and the constants and range variables themselves; formulas of $\mathcal{L}_{\mathrm{prob}}$ are Boolean combinations of comparisons $t \succsim t'$ of probability terms and of equalities between constants and range variables. The causal language $\mathcal{L}_{\mathrm{causal}}$ also allows interventional base formulas $[\mathbf{X} = \mathbf{x}]\,\delta$.

**Semantics.** Formulas are evaluated in recursive (acyclic), measurable structural causal models; a formula is valid in a model if it holds under every assignment of values to its free range variables, so free range variables are read universally. A model satisfies a sequent $\Gamma \Rightarrow \varphi$ if some formula of $\Gamma$ is not valid in it or $\varphi$ is valid in it. $\mathsf{SAT}_{\mathcal{L}}$ asks, for a finite set $\Gamma$ and a formula $\varphi$ of $\mathcal{L}$, whether some model in a fixed class satisfies $\Gamma \Rightarrow \varphi$. The classes are $\mathcal{M}$, all such models (recursive, measurable, countable and closed-world), and $\mathcal{M}_{\mathrm{fin}}$, those in which every variable has a finite range.

**Theorem (Ibeling, Icard and Mossé).** $\mathsf{SAT}_{\mathcal{L}_{\mathrm{prob}}}$ and $\mathsf{SAT}_{\mathcal{L}_{\mathrm{causal}}}$ are undecidable, both over $\mathcal{M}$ and over $\mathcal{M}_{\mathrm{fin}}$ (Theorem 2 of the source).

Over $\mathcal{M}_{\mathrm{fin}}$ both problems are recursively enumerable (Theorem 4). When every variable has the same fixed number $N$ of values, satisfiability for $\mathcal{L}_{\mathrm{causal}}(N)$ is complete for the class succ$\exists\mathbb{R}$ (Theorem 3), so undecidability comes from leaving the ranges unbounded together with the universal reading of free range variables.

## Depends on

- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)
- [Finite recursive structural causal model](../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/finite-scm.md)

## Proof depends on

None.

## Expansion

The proof encodes the conditional independence implication problem: a [conditional independence](../../random-fields/conditional-independence-on-finite-configuration/cond-indep.md) statement $\mathbf{X} \perp \mathbf{Y} \mid \mathbf{Z}$ is the formula $\mathbf{P}(\mathbf{x} \wedge \mathbf{y} \mid \mathbf{z}) \approx \mathbf{P}(\mathbf{x} \mid \mathbf{z}) \cdot \mathbf{P}(\mathbf{y} \mid \mathbf{z})$ with the value variables left free, and an implication between such statements becomes an entailment $\bigwedge_i p_i \vDash p_0$. Li proved that this implication problem is undecidable for random variables with finite, unbounded supports (Theorem 1 of the source, quoting Li's Theorem 3), which gives the result. Li's theorem has no page in this subject.

## Sources

- D. Ibeling, T. Icard and M. Mossé, "On probabilistic and causal reasoning with summation operators", Journal of Logic and Computation 35 (2025), no. 8, article exae068, https://doi.org/10.1093/logcom/exae068; read in arXiv:2405.03069v2 (Section 2, Definition of satisfiability, Theorems 1 to 4 and the discussion after Theorem 1 in the introduction of arXiv:2405.03069v2).
- C. T. Li, "Undecidability of network coding, conditional information inequalities, and conditional independence implication", IEEE Transactions on Information Theory 69 (2023), no. 6, 3493–3510, https://doi.org/10.1109/TIT.2023.3247570; read in arXiv:2205.11461v3 (Theorem 3 of arXiv:2205.11461v3).
