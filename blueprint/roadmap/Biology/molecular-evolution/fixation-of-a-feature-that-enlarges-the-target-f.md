# Mutational target size and fixation in a specified diffusion approximation

Fix an integer target size $n\ge0$ and a per-site lethal-hit probability
$0\le u<1$. Independent hits at the $n$ sites give the relative expected
contribution $w=(1-u)^n$ and the fitness deficit
$s=1-w\in[0,1)$, with $s\le nu$.
Adopt a Wright–Fisher **diffusion approximation**, with an integer copy
scale $M\ge1$, initial frequency $1/M$, and scaled coefficient $\sigma=-Ms$.
This choice of scaling is part of the model, not an exact finite-population
fixation formula. Write $U_\sigma$ for [Kimura's fixation function](../population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation.md).
The fixation probability relative to a neutral single copy is, for $s>0$,

$$R_M(s)=M U_{-Ms}(1/M)
 =\frac{M(e^{2s}-1)}{e^{2Ms}-1}
 =\frac{e^{2s}-1}{2s}\,g(2Ms),\qquad
 g(y)=\frac{y}{e^y-1}.$$

Set $g(0)=1$ and $R_M(0)=1$ by continuity. For $y\ge0$, $g$ is positive,
strictly decreasing on $(0,\infty)$, tends to zero at infinity, and
$g(y)\ge1-y/2$. Thus the exact diffusion-model comparison is

$$1-Mnu\le1-Ms\le g(2Ms)\le R_M(s)\le1.$$

Small $Mnu$ is sufficient for near-neutral relative fixation. For a sequence
with $M\to\infty$ and $Ms_M\to c\in[0,\infty)$,
$R_M(s_M)\to g(2c)$. At fixed $s>0$, $R_M(s)\to0$ as $M\to\infty$.
A large $Mnu$ alone is not a uniform limiting theorem: with $M=2$, $u=1/2$
and $n\to\infty$, $Mnu\to\infty$ but
$R_2(s)\to2/(1+e^2)>0$ because the fitness deficit saturates at one.
With $M=1$ the initial copy is already fixed and $R_1(s)=1$.

## Depends on

- [Kimura's fixation probability](../population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-fixation.md)

## Expansion

The union bound gives $s\le nu$. Substitute $\sigma=-Ms$, $x=1/M$
in Kimura's formula. For integer $M$, the geometric identity gives
$R_M(s)=M/\sum_{j=0}^{M-1}e^{2js}\le1$; the prefactor
$(e^{2s}-1)/(2s)\ge1$ gives the lower comparison.
The derivative numerator for $g$ is $e^y(1-y)-1$, strictly negative for
$y>0$ because its derivative is $-ye^y$.
To prove $g(y)\ge1-y/2$, it is automatic for $y\ge2$; for $0\le y<2$
use $\log((1+y/2)/(1-y/2))\ge y$, whose derivative is
$1/(1-y^2/4)\ge1$, then rearrange.
The limits follow directly from the exact formula.

## Sources

- M. Lynch and J. S. Conery, "The origins of genome complexity", Science 302 (2003), 1401--1404, <https://doi.org/10.1126/science.1089370>, abstract. The claim that genome complexity largely arose through passive population-size effects is an empirical explanatory hypothesis. The target model and qualified diffusion comparison above are derived here, not a universal proof of that hypothesis.
