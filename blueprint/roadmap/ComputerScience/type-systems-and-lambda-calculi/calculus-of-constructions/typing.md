# Typing judgement of the calculus of constructions with universes

A context $\Gamma$ is a
list of terms whose head is the type of the most recent variable; write $\Gamma, A$ for
$\Gamma$ extended by $A$ at the head. The judgement $\Gamma \vdash t : A$ ($t$ has type $A$
in $\Gamma$) is defined together with well-formedness of contexts as the least relation
closed under the following rules.

* Sorts: if $\Gamma$ is well formed and $s : s'$ is an axiom, namely
  $\mathrm{Prop} : \mathrm{Type}_0$ or $\mathrm{Type}_i : \mathrm{Type}_{i+1}$, then
  $\Gamma \vdash s : s'$.
* Variables: if $\Gamma$ is well formed and its entry at position $i$ (counting from $0$ at
  the head) is $A$, then $\Gamma \vdash \#i : A'$, where $A'$ is $A$ with every free variable
  raised by $i + 1$.
* Products: if $\Gamma \vdash A : s_1$, $\Gamma, A \vdash B : s_2$ and $(s_1, s_2, s_3)$ is a
  product rule, namely $(s, \mathrm{Prop}, \mathrm{Prop})$ for a sort $s$,
  $(\mathrm{Type}_i, \mathrm{Type}_j, \mathrm{Type}_{\max(i, j)})$ or
  $(\mathrm{Prop}, \mathrm{Type}_i, \mathrm{Type}_i)$, then
  $\Gamma \vdash \Pi (x : A).\, B : s_3$.
* Abstractions: if $\Gamma \vdash \Pi (x : A).\, B : s$ for some sort $s$ and
  $\Gamma, A \vdash b : B$, then $\Gamma \vdash \lambda (x : A).\, b : \Pi (x : A).\, B$.
* Applications: if $\Gamma \vdash f : \Pi (x : A).\, B$ and $\Gamma \vdash a : A$, then
  $\Gamma \vdash f\,a : B[a]$, where $B[a]$ replaces variable $0$ of $B$ by $a$ and lowers
  the other free variables of $B$ by one.
* Conversion: if $\Gamma \vdash t : A$, $\Gamma \vdash B : s$ for some sort $s$, and $A$ and
  $B$ are beta convertible, then $\Gamma \vdash t : B$.
