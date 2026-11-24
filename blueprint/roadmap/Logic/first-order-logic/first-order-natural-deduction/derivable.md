# Natural deduction

Fix a first-order language $L$ and a type $\alpha$ of variables;
formulas and terms below are those of $L$ with free variables in $\alpha$. For a formula
$\varphi$ with one additional bound variable and a term $t$, write $\varphi[t]$ for $\varphi$
with $t$ substituted for that bound variable and $\forall \varphi$ for its universal
quantification. Write $\neg \psi$ for $\psi \to \bot$, and $\psi, \Gamma$ for the list $\Gamma$
with $\psi$ added in front. Derivability $\Gamma \vdash \varphi$ of a formula $\varphi$ (the
conclusion) from a finite list $\Gamma$ of formulas (the open hypotheses) is the least relation
closed under the following rules.

* Assumption: $\Gamma \vdash \varphi$ whenever $\varphi$ is a member of $\Gamma$.
* Implication introduction: from $\varphi, \Gamma \vdash \psi$ infer
  $\Gamma \vdash \varphi \to \psi$.
* Implication elimination: from $\Gamma \vdash \varphi \to \psi$ and $\Gamma \vdash \varphi$
  infer $\Gamma \vdash \psi$.
* Reductio ad absurdum: from $\neg \varphi, \Gamma \vdash \bot$ infer $\Gamma \vdash \varphi$.
* Universal introduction: if a variable $x$ occurs free in no member of $\Gamma$ and does not
  occur free in $\varphi$, then from $\Gamma \vdash \varphi[x]$ infer
  $\Gamma \vdash \forall \varphi$.
* Universal elimination: from $\Gamma \vdash \forall \varphi$ infer $\Gamma \vdash \varphi[t]$,
  for every term $t$.
* Reflexivity: $\Gamma \vdash t = t$ for every term $t$.
* Substitution: from $\Gamma \vdash s = t$ and $\Gamma \vdash \varphi[s]$ infer
  $\Gamma \vdash \varphi[t]$.
