# Lifting System F type-variable images under a star binder

For a kinding context $\Delta$ and a map $\varphi$ assigning to each $i < n$ a type $\varphi(i) \in
\mathrm{Ty}^{\star}_{\Delta}$ of kind $\star$, the lifted map $\varphi^{\uparrow}$ assigns to each
$i < n + 1$ a type in $\mathrm{Ty}^{\star}_{\star \cdot \Delta}$: $\varphi^{\uparrow}(0) = \alpha_0$
and $\varphi^{\uparrow}(i+1) = \varphi(i)\langle\uparrow\rangle$, the image
[renamed](../intrinsically-kinded-type-operators-for-pure-f/rename.md) by the successor renaming.
