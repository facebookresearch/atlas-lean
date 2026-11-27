# A security type system enforces gradual release

Type the [language with low events](attacker-knowledge.md) by judgements $\Gamma \vdash e : \sigma$ and $\Gamma, pc \vdash c$ over the levels $L \sqsubseteq H$ with the standard
rules: a constant has level $L$, a variable $x$ has level $\Gamma(x)$ and $e_1 \mathbin{op} e_2$ has the join of the levels of its operands; $x := e$ requires
$pc \sqcup \sigma \sqsubseteq \Gamma(x)$ where $\Gamma \vdash e : \sigma$; sequencing types both parts at $pc$; a conditional or loop with guard of level $\sigma$ types its
branches or body at $pc \sqcup \sigma$; and $x := \mathrm{declassify}(e)$ requires only $pc \sqsubseteq \Gamma(x)$, so declassification to a low variable is forbidden inside
conditionals and loops with high guards.

**Theorem.** If $\Gamma, pc \vdash c$, then $c$ satisfies [gradual release](gradual-release.md).

## Depends on

- [Gradual release](gradual-release.md)

## Sources

- A. Askarov and A. Sabelfeld, "Gradual release: unifying declassification, encryption and key release policies", *Proceedings of the 2007 IEEE Symposium on Security and Privacy*, copy at <https://www.cs.cornell.edu/~aslan/askarov-sabelfeld-sp07.pdf>: Section 2, Figure 3 (type rules for the simple language), the rule (T-DECL) and Theorem 1.
