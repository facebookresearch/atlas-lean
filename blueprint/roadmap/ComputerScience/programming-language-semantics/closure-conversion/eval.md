# Big-step semantics of the closure-conversion source

Evaluation
$\rho \vdash t \Downarrow v$ of a raw term $t$ to a source value $v$ in an environment $\rho$ (a
list of source values, where variable $n$ refers to the entry of $\rho$ at index $n$, counting
from $0$) is the least relation closed under the following rules, a call-by-value environment
semantics that ignores the type annotations of lambdas. A variable $n$ evaluates to the entry of
$\rho$ at index $n$, when that entry exists. A lambda $\lambda. b$ evaluates to the closure of $b$
over $\rho$. If $f$ evaluates in $\rho$ to the closure of $b$ over $\rho'$, if
$\rho \vdash a \Downarrow v$, and if $v :: \rho' \vdash b \Downarrow w$, where $v :: \rho'$ is
$\rho'$ with $v$ added at index $0$, then $\rho \vdash f\,a \Downarrow w$.
