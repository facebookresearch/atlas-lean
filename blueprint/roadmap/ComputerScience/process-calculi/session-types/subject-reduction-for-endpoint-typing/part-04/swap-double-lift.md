# Swapping the two innermost binders fixes a twice-lifted context

For every ownership context $\Delta$, $(\uparrow_0\uparrow_0\Delta)[0 \leftrightarrow 1] =
\uparrow_0\uparrow_0\Delta$: after two liftings at cutoff $0$ no endpoint name is $\mathrm{v}_0$ or
$\mathrm{v}_1$, so exchanging these two variables changes nothing.
