# SCPAC learnability

A class of computable hypotheses is SCPAC learnable (strongly computably PAC learnable) when some total computable learner, together with a total computable sample-size function, agnostically PAC learns it. Requiring the sample complexity to be computable is what distinguishes it from CPAC learnability.

**Setting.** The domain is $\mathcal{X} = \mathbb{N}$ and the label set is $\mathcal{Y} = \{0, 1\}$. A hypothesis is a total computable function $h : \mathbb{N} \to \{0,1\}$; a hypothesis class $\mathcal{H}$ is a set of hypotheses. A sample is a finite sequence $S \in \bigcup_{n} (\mathcal{X} \times \mathcal{Y})^n$. For a probability distribution $\mathcal{D}$ on $\mathcal{X} \times \mathcal{Y}$ the risk of $h$ is

$$
L_{\mathcal{D}}(h) = \Pr_{(x,y) \sim \mathcal{D}}[h(x) \ne y].
$$

**Definition (Sterkenburg).** $\mathcal{H}$ is *SCPAC learnable* if one can find a total computable function $A$ from samples to $\mathcal{H}$ and a total computable function $m_{\mathcal{H}} : \mathbb{N}^2 \to \mathbb{N}$ such that for all $a, b \in \mathbb{N}$ (with $a, b \ge 1$), all $m \ge m_{\mathcal{H}}(a, b)$ and every distribution $\mathcal{D}$ on $\mathcal{X} \times \mathcal{Y}$,

$$
\Pr_{S \sim \mathcal{D}^m}\Bigl[L_{\mathcal{D}}(A(S)) > \inf_{h \in \mathcal{H}} L_{\mathcal{D}}(h) + \tfrac{1}{a}\Bigr] < \tfrac{1}{b}.
$$

(The source writes $\min$ for the infimum.) Dropping the requirement that $m_{\mathcal{H}}$ be computable (keeping only that $A$ is total computable and PAC learns $\mathcal{H}$ in the agnostic, proper sense) gives *CPAC learnability* in the sense of Agarwal, Ananthakrishnan, Ben-David, Lechner and Urner.

## Depends on

- [Learners and agnostic PAC learnability](../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

None.

## Expansion

Sterkenburg shows that a nonempty hypothesis class is SCPAC learnable if and only if it has finite VC dimension and some algorithm implements empirical risk minimization for it (returns, for each sample, a hypothesis of $\mathcal{H}$ with least empirical error). The learner is proper: it outputs hypotheses in $\mathcal{H}$. The quantities $1/a$ and $1/b$ play the roles of $\epsilon$ and $\delta$ in the usual definition, restricted to reciprocals of positive integers so that $m_{\mathcal{H}}$ can be a computable function on natural numbers. The sufficient condition comes from Sauer's lemma, which bounds the sample complexity of uniform convergence by a computable function of the VC dimension and the accuracy and confidence parameters, the VC dimension being the only parameter that depends on the class.

## Sources

- Tom F. Sterkenburg, "On characterizations of learnability with computable learners", Proceedings of the Thirty Fifth Conference on Learning Theory (COLT 2022), Proceedings of Machine Learning Research 178, pp. 3365–3379, 2022; Definition 5 (SCPAC learnability), Definition 4 (CPAC learnability), Proposition 1 and Theorem 2 (characterization) of arXiv:2202.05041v2, <https://arxiv.org/abs/2202.05041v2>.
