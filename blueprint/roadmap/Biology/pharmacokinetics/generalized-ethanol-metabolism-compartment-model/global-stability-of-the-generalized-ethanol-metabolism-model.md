# Global stability of the generalized ethanol metabolism model

**Model.** Let $A(t)$, $B(t)$, $C(t)$ be the amounts of ethanol in the gastrointestinal tract, the blood and the liver. Ethanol is absorbed from the gut at rate $a>0$, exchanges between blood and liver at rate $b>0$, and is metabolized in the liver at a nonlinear rate $f(C)$:

$$A'=-aA,\qquad B'=bC-bB+aA,\qquad C'=bB-bC-f(C),$$

with $A(0)>0$, $B(0)\ge0$, $C(0)\ge0$. The rate function satisfies

**(P)** $f$ is continuous on $[0,\infty)$, $f(x)\ge0$ for $x\ge0$, and $f(x)=0$ if and only if $x=0$.

The Michaelis–Menten choice $f(C)=cC/(d+C)$ recovers the earlier three-compartment model; (P) also allows Hill-type, exponential-saturation and other bounded rates reflecting the finite capacity of alcohol dehydrogenase.

**Lemma (positivity and monotonicity).** The orthant $\Omega=\{(A,B,C)\in\mathbb{R}^3:A,B,C\ge0\}$ is positively invariant, and both $A(t)$ and the total body load $S(t)=A(t)+B(t)+C(t)$ are nonincreasing; indeed $S'(t)=-f(C(t))\le0$.

**Theorem.** Under (P) the origin $E^*=(0,0,0)$ is the unique equilibrium, and it is globally asymptotically stable on $\Omega$: every nonnegative solution satisfies $(A,B,C)(t)\to(0,0,0)$ as $t\to\infty$.

Biologically, any ingested dose is eventually cleared, whatever the shape of the hepatic metabolism curve, as long as the liver metabolizes at a positive rate whenever ethanol is present.

## Expansion

Equilibria satisfy $aA=0$, $bC-bB=0$ and $bB-bC=f(C)$, so $f(C)=0$, which forces $C=0$ and then $B=0$. The gut equation integrates to $A(t)=A(0)e^{-at}\to0$, so the system is a cascade: a globally stable driving subsystem feeding the $(B,C)$ subsystem. For the limiting subsystem $B'=b(C-B)$, $C'=b(B-C)-f(C)$, the quadratic Lyapunov function $V=\tfrac12(B^2+C^2)$ has

$$\dot V=-b(B-C)^2-Cf(C)\le0 ,$$

with equality only at $B=C=0$, so $(0,0)$ is globally asymptotically stable there. Results on global stability of cascade-connected nonlinear systems (bounded trajectories, guaranteed here by the monotone total load) then transfer global stability to the full system.

## Depends on

- [Saturable Michaelis–Menten elimination](../saturable-michaelis-menten-elimination/README.md)

## Sources

- Manh Tuan Hoang, Thi Kim Quy Ngo, Benjamin Wacker, "On a Generalized Compartment Model for Ethanol Metabolism in the Human Body", arXiv:2606.30439 (2026): model and property (P) in Section 1, Lemma 2.1 (positive invariance, monotone load), Theorem 2.2 (global asymptotic stability). <https://doi.org/10.48550/arXiv.2606.30439>
