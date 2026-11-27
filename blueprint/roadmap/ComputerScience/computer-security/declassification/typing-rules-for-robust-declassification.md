# Typing rules for robust declassification

Use the product lattice, attacker point $A$, language and indistinguishability relations of [robust declassification](robust-declassification.md), with the high-integrity
levels $H_I = \{\ell \mid I(A) \not\sqsubseteq I(\ell)\}$ and low-confidentiality levels $L_C = \{\ell \mid C(\ell) \sqsubseteq C(A)\}$. Expressions are typed by $\Gamma \vdash e : \ell$: values have
any level, a variable $v$ has $\Gamma(v)$, $e \mathbin{op} e'$ has the level of both operands, and levels may be raised by subsumption. Commands are typed by $\Gamma, pc \vdash c$:

- $\mathbf{skip}$ is typable at any $pc$; $v := e$ needs $\Gamma \vdash e : \ell$ with $\ell \sqcup pc \sqsubseteq \Gamma(v)$; sequencing types both parts at $pc$;
- $\mathbf{if}\ e\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$ and $\mathbf{while}\ e\ \mathbf{do}\ c$ need $\Gamma \vdash e : \ell$ and type the branches or body at $\ell \sqcup pc$; a command typable at $pc$ is typable at
  any $pc' \sqsubseteq pc$;
- $v := \mathrm{declassify}(e, \ell)$ needs $\Gamma \vdash e : \ell'$, $\ell \sqcup pc \sqsubseteq \Gamma(v)$, $I(\ell) = I(\ell')$ and $pc, \ell' \in H_I$;
- a hole $\bullet$ is typable when $pc \in L_C$.

A command $a$ is an *$A$-attack* if $\Gamma, (\bot_C, I(A)) \vdash a$ and $\mathrm{declassify}$ does not occur in $a$.

## Depends on

- [Robust declassification](robust-declassification.md)

## Sources

- A. C. Myers, A. Sabelfeld and S. Zdancewic, "Enforcing robust declassification and qualified robustness", *Journal of Computer Security* 14(2), 2006, copy at <https://www.cse.chalmers.se/~andrei/msz-jcs.pdf>: Section 5, Figure 4 (typing rules), the typing rule for holes and Definition 10 ($A$-attacks).
