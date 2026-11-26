# Small-step reduction of Featherweight Java

Single-step reduction $e \to e'$ in a class table is the least relation closed under the following rules, where $\bar v$ and $\bar u$ are argument lists of [values](value.md) and $<:$ is [subtyping](subtype.md).

- E-PROJ: if [field lookup](fields.md) gives a list $fs$ for $C$ and the [positional field lookup](field-value.md) of $f$ in $fs$ and $\bar v$ gives $v$, the argument paired with the first field named $f$, then $\mathtt{new}\ C(\bar v).f \to v$.
- E-INVK: if [method body lookup](mbody.md) gives parameter names $x_1, \dots, x_n$ and body $e$ for $m$ in $C$, and $\bar u = u_1, \dots, u_n$ has exactly $n$ entries, then $\mathtt{new}\ C(\bar v).m(\bar u) \to e[\mathtt{this} := \mathtt{new}\ C(\bar v), x_1 := u_1, \dots, x_n := u_n]$, a [simultaneous substitution](subst-many.md) in which the first binding of a name wins.
- E-CAST: if $C <: D$, then $(D)\,\mathtt{new}\ C(\bar v) \to \mathtt{new}\ C(\bar v)$. A cast whose runtime class is not a subtype of the target does not reduce.
- Congruence (E-CONTEXT): if $e \to e'$, then $e.f \to e'.f$, $e.m(\bar a) \to e'.m(\bar a)$ and $(C)\,e \to (C)\,e'$; if an argument list $\bar a$ steps to $\bar a'$, then $\mathtt{new}\ C(\bar a) \to \mathtt{new}\ C(\bar a')$ and, when the receiver is a value $\mathtt{new}\ C(\bar v)$, $\mathtt{new}\ C(\bar v).m(\bar a) \to \mathtt{new}\ C(\bar v).m(\bar a')$. An [argument list steps](args-step.md) at its leftmost non-value entry, all entries to its left being values.

So the receiver is evaluated before the arguments, and the arguments from left to right; the resulting relation is [deterministic](deterministic.md).
