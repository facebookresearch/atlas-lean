# Logic of functional dependence

The logic of functional dependence LFD extends a relational first-order language, evaluated at assignments drawn from a fixed set of admissible ones, by dependence atoms $D_X y$ (the values of $X$ determine the value of $y$) and dependence modalities $\mathbb{D}_X\varphi$ (the values of $X$ determine the truth of $\varphi$).

**Models.** A *dependence model* is $\mathbf{M} = (M, A)$ where $M = (O, I)$ is a relational first-order structure with domain $O$ and $A \subseteq O^V$ is a set of *admissible assignments* of objects to the variables $V$. It is *full* if $A = O^V$. For $X \subseteq V$, assignments $s, t$ *agree on $X$*, $s =_X t$, if $s(x) = t(x)$ for all $x \in X$.

**Syntax.** For a vocabulary of variables and predicate symbols,

$$
\varphi ::= P\mathbf{x} \mid \neg\varphi \mid \varphi \wedge \varphi \mid \mathbb{D}_X\varphi \mid D_X y
$$

with $X$ a finite set of variables, $y$ a variable and $\mathbf{x}$ a tuple of variables of the arity of $P$.

**Semantics** at $s \in A$: $P\mathbf{x}$ is true iff $s(\mathbf{x}) \in I(P)$; Booleans as usual; $\mathbb{D}_X\varphi$ is true iff $\varphi$ is true at every $t \in A$ with $s =_X t$; and $D_X y$ is true iff every $t \in A$ with $s =_X t$ has $s =_y t$. Validity means truth at every assignment of every dependence model. $\mathbb{D}_\varnothing$ is the universal modality.

**Independence.** For sets $X, Y$ of variables, the information $X$ carries about $Y$ at $s$ is $\mathrm{Inf}_s(X, Y) = \{t \restriction Y : t \in A, t =_X s\}$, and the *independence atom* $I_X Y$ is true at $s$ iff $\mathrm{Inf}_s(X, Y) = \mathrm{Inf}_s(\varnothing, Y)$. LFDI is LFD extended with the atoms $I_X y$.

## Depends on

None.

## Proof depends on

None.

## Expansion

LFD translates effectively into first-order logic, so its validities are recursively enumerable; the source gives a complete axiomatization and proves LFD decidable, by a filtration-style argument with Hintikka sets. The dependence modalities generalize the quantifiers of the cylindric relativized set (CRS) semantics, and on full models they behave like first-order quantifiers.

## Sources

- A. Baltag and J. van Benthem, "A simple logic of functional dependence", *Journal of Philosophical Logic* 50(5):939–1005, 2021, doi:10.1007/s10992-020-09588-z; read as arXiv:2103.14946v1, <https://arxiv.org/abs/2103.14946v1>: Definitions 2.1–2.2 (dependence models, agreement and local dependence), Definitions 3.1–3.2 (syntax and semantics of LFD) and the definitions of information and independence atoms in Section 6.
