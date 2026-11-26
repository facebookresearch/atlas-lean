# Heat Solution family continuous On

Let $T\ge0$, and let $f:[0,T]\times\mathbb R\to\mathbb R$ be jointly continuous.
Suppose there exist $M,c\ge0$ with $|f(s,x)|\le M e^{c|x|}$ for all
$s\in[0,T]$ and $x\in\mathbb R$. Then

$$
(s,h,x)\longmapsto P_h(f(s,\cdot))(x)
$$

is jointly continuous on $[0,T]\times\mathbb R\times\mathbb R$.
Here $P_h$ is the Gaussian heat evolution at positive heat times and the
stationary extension $P_hg=g$ for $h\le0$. Thus continuity includes zero and
negative heat times; no backward heat equation or time derivative at zero is
asserted. No continuity of $f$ outside its parameter strip is required.

The proof uses fixed-Gaussian rescaling, local exponential domination, and a
continuous clamp of the family parameter.
