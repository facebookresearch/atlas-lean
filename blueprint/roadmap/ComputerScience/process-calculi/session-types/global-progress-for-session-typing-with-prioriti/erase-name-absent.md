# Erasing a key whose name is absent preserves ranked typing

Let $n$ be a natural number, $\Delta$ an ownership context, $p$ a process and $z$ an endpoint whose
name $x$ does not occur in $p$ (in no subject or payload position, where under each binder of $p$
the index of $x$, if it is a variable, is raised by one). If $\Delta \vdash^{\mathrm{rk}}_n p$, then
$\Delta \setminus z \vdash^{\mathrm{rk}}_n p$.
