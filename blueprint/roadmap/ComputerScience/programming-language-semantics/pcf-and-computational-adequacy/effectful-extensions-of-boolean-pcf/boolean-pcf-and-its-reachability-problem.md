# Boolean PCF and its reachability problem

Boolean PCF is the simply typed call-by-value λ-calculus over the base types unit and bool with recursion, conditionals and an error command $\mathbf{fail}$; its reachability problem asks whether a closed program of base type can reduce to $\mathbf{fail}$.

**Syntax.** Types are $\tau ::= b \mid \tau_1 \to \tau_2$ with base types $b ::= \mathbf{unit} \mid \mathbf{bool}$. Expressions and values are

$$
M ::= \mathbf{fail} \mid V \mid x \mid M_1\,M_2 \mid \mathbf{fix}(f, x, M) \mid \mathbf{if}\ M_0\ \mathbf{then}\ M_1\ \mathbf{else}\ M_2, \qquad V ::= () \mid \mathbf{true} \mid \mathbf{false} \mid \lambda x.M,
$$

where $\mathbf{fix}(f, x, M)$ is the recursive function $f$ with $f(x) = M$. Typing is the standard simple typing, with $\mathbf{fail}$ of every type. Evaluation is call-by-value small-step reduction $\longrightarrow$ in evaluation contexts; $\longrightarrow^*$ is its reflexive transitive closure.

**Reachability.** The *reachability problem* for Boolean PCF, or for an extension of it, is: given a closed expression $M$ with $\vdash M : b$ for a base type $b$, decide whether $M \longrightarrow^* \mathbf{fail}$.

## Depends on

None.

## Proof depends on

None.

## Expansion

All base types are finite, so Boolean PCF is a finitary language; its reachability problem is decidable, as an immediate consequence of the decidability of higher-order model checking (Ong; Kobayashi). This is not the functional reachability problem of Ong and Tzevelekos, which quantifies over contexts and is undecidable in general. The same reachability question can be posed for extensions with exceptions, algebraic effects and handlers, symbol generation with equality, or references, each adding expressions, types and reduction rules; the decidability of higher-order model checking does not extend to them. Call-by-value is chosen for convenience in adding effects; for pure Boolean PCF the call-by-name version has the same decidability status.

## Sources

- Naoki Kobayashi, "On Decidable and Undecidable Extensions of Simply Typed Lambda Calculus", *Proceedings of the ACM on Programming Languages* 9(POPL), 2025, pp. 1136–1166, <https://doi.org/10.1145/3704875>; read as arXiv:2411.06086v2, <https://arxiv.org/abs/2411.06086v2>: the subsection "Boolean PCF" (syntax, typing and reduction rules, the definition of the reachability problem and the remarks after it) of that version.
