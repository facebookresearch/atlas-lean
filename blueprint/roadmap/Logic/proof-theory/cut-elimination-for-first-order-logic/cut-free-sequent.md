# The cut-free sequent calculus for first-order logic

Fix a first-order language $L$ and an infinite set $X$ of variables with decidable equality. A sequent $\Gamma \Rightarrow \varphi$ consists of a finite list $\Gamma$ of $L$-formulas with free variables in $X$ and one such formula $\varphi$; $\varphi, \Gamma$ denotes the list $\Gamma$ with $\varphi$ added in front, and $\varphi(t)$ denotes the result of substituting the term $t$ for the bound variable of a one-variable body $\varphi(y)$.

Cut-free derivability is the smallest relation on sequents closed under the following rules; it is the classical sequent calculus with the cut rule removed, keeping reductio and the equality rules.

- (Assumption) $\Gamma \Rightarrow \varphi$ whenever $\varphi \in \Gamma$.
- (Ex falso) $\Gamma \Rightarrow \varphi$ whenever $\bot \in \Gamma$.
- ($\to$ right) From $\varphi, \Gamma \Rightarrow \psi$ infer $\Gamma \Rightarrow \varphi \to \psi$.
- ($\to$ left) From $\Gamma \Rightarrow \varphi$ and $\psi, \Gamma \Rightarrow \chi$ infer $\varphi \to \psi, \Gamma \Rightarrow \chi$.
- ($\forall$ right) If $x \in X$ is free neither in any formula of $\Gamma$ nor in $\forall y\, \varphi(y)$, from $\Gamma \Rightarrow \varphi(x)$ infer $\Gamma \Rightarrow \forall y\, \varphi(y)$.
- ($\forall$ left) For any term $t$, from $\varphi(t), \Gamma \Rightarrow \psi$ infer $\forall y\, \varphi(y), \Gamma \Rightarrow \psi$.
- (Reductio) From $\neg \varphi, \Gamma \Rightarrow \bot$ infer $\Gamma \Rightarrow \varphi$, where $\neg \varphi$ is $\varphi \to \bot$.
- (Reflexivity) $\Gamma \Rightarrow t = t$ for every term $t$.
- (Substitution) From $\Gamma \Rightarrow s = t$ and $\Gamma \Rightarrow \varphi(s)$ infer $\Gamma \Rightarrow \varphi(t)$.

The left rules ($\to$ left and $\forall$ left) act only on the first formula of the context, and there are no weakening, exchange or contraction rules; assumption and ex falso apply to any member of the context.
