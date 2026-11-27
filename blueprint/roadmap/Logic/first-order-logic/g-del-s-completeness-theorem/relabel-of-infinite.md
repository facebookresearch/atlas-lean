# Renaming free variables along an arbitrary map preserves derivability

Let $\alpha$ and
$\beta$ be types of variables with $\beta$ infinite, and let $f : \alpha \to \beta$ be any map.
If $\varphi$ is derivable from the list of hypotheses $\Gamma$ in natural deduction, then the
formula obtained from $\varphi$ by renaming each free variable $x$ to $f(x)$ is derivable from
the list obtained by renaming the free variables of each formula of $\Gamma$ in the same way.

The map need not be injective: in the proof each eigenvariable is sent to a fresh variable.
