# Substitution for type variable zero

Consider the call-by-value lambda calculus with iso-recursive types. Its types are $\mathrm{unit}$, arrows $a \to b$, de Bruijn type variables $X_n$ ($n \in \mathbb{N}$) and recursive types $\mu.\,a$, where $\mu$ binds type index $0$ in $a$. Its terms are $\mathrm{unit}$, de Bruijn variables $x_n$, abstractions $\lambda.\,t$ without a type annotation (binding index $0$ in $t$), applications $t\,u$, and $\mathrm{fold}\,t$ and $\mathrm{unfold}\,t$, neither annotated with a type.

For a type $a$, an index $j \in \mathbb{N}$ and a type $s$, the substitution $a[j := s]$ is defined by recursion on $a$: $\mathrm{unit}[j := s] = \mathrm{unit}$; $(a \to b)[j := s] = a[j := s] \to b[j := s]$; $X_n[j := s]$ is $X_n$ if $n < j$, $s$ if $n = j$, and $X_{n-1}$ if $n > j$; and $(\mu.\,a)[j := s] = \mu.\,\bigl(a[j+1 := \uparrow^1_0 s]\bigr)$, where $\uparrow^d_c$ adds $d$ to every type variable of index at least $c$ (and increases the cutoff $c$ by one under each $\mu$).

The type substitution of $s$ into $a$ is the case $j = 0$: it is $a[0 := s]$, which substitutes $s$ for type variable $0$ (the variable bound by an enclosing $\mu$) and lowers the other free type variables by one.

## Sources

- B. C. Pierce, *Types and Programming Languages*, MIT Press, 2002, Chapter 20 (iso-recursive types). In that presentation $\mathrm{fold}$ and $\mathrm{unfold}$ carry the recursive type as an annotation; here they are unannotated.
