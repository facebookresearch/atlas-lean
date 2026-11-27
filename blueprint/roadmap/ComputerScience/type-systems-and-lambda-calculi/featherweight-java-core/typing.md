# Expression typing

Expression typing $\Gamma \vdash e : C$ in a class table, for a typing context $\Gamma$ (a partial map from variables to class names), is the least relation closed under the following rules, where $<:$ is [subtyping](subtype.md).

- T-VAR: $\Gamma \vdash x : C$ when $\Gamma(x) = C$.
- T-FIELD: if $\Gamma \vdash e : C$, [field lookup](fields.md) gives a list $fs$ for $C$ and $(C_i, f)$ is an entry of $fs$, then $\Gamma \vdash e.f : C_i$.
- T-INVK: if $\Gamma \vdash e : C$, [method type lookup](mtype.md) gives parameter classes $B_1, \dots, B_n$ and result class $B_0$ for $m$ in $C$, and the arguments are $n$ expressions $e_i$ with $\Gamma \vdash e_i : A_i$ and $A_i <: B_i$, then $\Gamma \vdash e.m(e_1, \dots, e_n) : B_0$.
- T-NEW: if field lookup gives the fields $(C_1, f_1), \dots, (C_n, f_n)$ for $C$ and the arguments are $n$ expressions $e_i$ with $\Gamma \vdash e_i : A_i$ and $A_i <: C_i$, then $\Gamma \vdash \mathtt{new}\ C(e_1, \dots, e_n) : C$.
- T-UCAST: if $\Gamma \vdash e : D$ and $D <: C$, then $\Gamma \vdash (C)\,e : C$.
- T-DCAST: if $\Gamma \vdash e : D$, $C <: D$ and $C \ne D$, then $\Gamma \vdash (C)\,e : C$.
- T-SCAST: if $\Gamma \vdash e : D$ and neither $C <: D$ nor $D <: C$, then $\Gamma \vdash (C)\,e : C$.

So a cast between unrelated classes is well typed. Whether a cast can reduce is decided at run time by the cast rule of [reduction](step.md), which requires the runtime class to be a subtype of the target.
