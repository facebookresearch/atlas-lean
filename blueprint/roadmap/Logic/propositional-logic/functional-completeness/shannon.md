# Shannon expansion

Let $f$ assign a truth value to every valuation of the atoms. The
Shannon expansion $S(\ell, f)$ of $f$ over a list $\ell$ of atoms is defined by recursion on
$\ell$. For the empty list it is $\bot \to \bot$ if $f$ is true at the valuation that makes every
atom false, and $\bot$ otherwise. For the list $x \cdot \ell$ with head $x$ and tail $\ell$,

$$
S(x \cdot \ell, f) = (x \wedge S(\ell, f_1)) \vee (\neg x \wedge S(\ell, f_0)),
$$

where $\neg x$ is $x \to \bot$, and $f_1(v) = f(v[x \mapsto \mathrm{true}])$ and
$f_0(v) = f(v[x \mapsto \mathrm{false}])$, with $v[x \mapsto b]$ the valuation $v$ changed at $x$
to $b$.
