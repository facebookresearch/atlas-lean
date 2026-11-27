# Periodic orbit of the piecewise-affine sequestration clock

**Model.** The skeleton clock model has activator CLOCK:BMAL1 ($B$), DBP ($D$), REV-ERB ($R$) and repressor PER:CRY ($P$):

$$\dot B=V_Rh(R)-\gamma_BBP,\quad \dot D=V_BB-\gamma_DD,\quad \dot R=V_DD-\gamma_RR,\quad \dot P=V_DD-\gamma_BBP,\quad h(R)=\frac{k_R^2}{k_R^2+R^2}.$$

After nondimensionalization, the difference $x=b-p$ of activator and repressor governs the dynamics. In the limit of infinitely fast sequestration the two species cannot coexist, so the free activator is $f_b(x)=\max\{x,0\}$. Replacing the Hill function by a switch gives the piecewise-affine (PWA) system

$$\dot x=h_s(r)-\epsilon d,\qquad \dot d=f_b(x)-\beta d,\qquad \dot r=\gamma d-\delta r,\qquad h_s(r)=\mathbf 1\{r<1\},$$

with $\beta,\gamma,\delta,\epsilon>0$. Its threshold surfaces $r=1$, $x=0$ and $d=d^*=\delta/\gamma$ cut the state space into regions labeled R/r ($r>1$ or $r<1$), X/x ($x>0$ or $x<0$) and D/d ($d>d^*$ or $d<d^*$), and each region carries a linear time-invariant subsystem.

**Assumption 3.1.** $\gamma>\epsilon\delta$, equivalently $\epsilon d^*<1$; then $d<d^*$ implies $\dot x>0$. Under this assumption the transitions RxD$\to$Rxd$\to$rxd$\to$rXd$\to$rXD are forced.

**Theorem 3.5.** If stage rXD is entered from rXd and

$$\sqrt{\frac{2}{\gamma(\underline x-\beta/\epsilon)}}<\frac{\sqrt{G^2+2H^2/\epsilon}-G}{H},$$

where $H=1-\epsilon d^*$, $\underline x=H\sqrt{d^*}$ is a lower bound for $x$ at the transition rXd$\to$rXD (Lemma 7.2), $\overline x=\big(\sqrt{\beta^2d^{*2}+2Hd^*}-\beta d^*\big)/H$ is an upper bound (Lemma 7.1) and $G=\overline x-\beta d^*$, then the only possible exit is to RXD. The left side bounds from above the time for $r$ to reach $1$, and the right side bounds from below the time for $d$ to reach $1/\epsilon$, which must happen before $x$ or $d$ can cross its threshold.

**Theorem 3.7.** In region RXD, where $\dot x=-\epsilon d$ and $\dot d=x-\beta d$, let $F=\beta\underline x/(\epsilon-\beta^2)$ and

$$x_m(t_1)=\underline x\exp\!\Big(-\frac{\epsilon}{\beta^2-\epsilon}\ln\Big(\beta\,\frac{d^*+F}{\underline x+\beta F}\Big)\Big),$$

the value of $x$ at which the trajectory of the comparison system $\dot x=-\epsilon x/\beta$, $\dot d=x-\beta d$ started at $(\underline x,d^*)$ meets the line $x=\beta d$. If

$$x_m(t_1)\Big(\frac1\beta-\frac{x_m(t_1)}{2\epsilon d^*}\Big)>d^*,$$

then the bounding Jordan curve used to track trajectories from RXD ends on $\{x=0,\ d>d^*\}$, so $d$ cannot fall below $d^*$ in RXD and the only possible exit is RXD$\to$RxD.

**Corollary 3.8.** Under Assumption 3.1 and the hypotheses of Theorems 3.5 and 3.7, the only possible itinerary is the cycle RxD$\to$Rxd$\to$rxd$\to$rXd$\to$rXD$\to$RXD$\to$RxD; if all solutions stay bounded, the return map on a section of the transition RXD$\to$RxD has a fixed point and the PWA system has a periodic orbit.

## Expansion

Each region's subsystem is linear, so trajectories are explicit and the times and values at region crossings can be bounded (Lemmas 7.1–7.2 bound $x$ after stage rXd). Excluding every alternative exit from each region leaves a single cyclic itinerary. A compact convex subset of the section through the transition RXD$\to$RxD, avoiding the equilibrium, is then mapped into itself by the first-return map, and Brouwer's fixed-point theorem gives a periodic orbit. The sequestration loop acts like a Goodwin oscillator in which degradation of the activator is replaced by stoichiometric titration against its repressor.

## Sources

- B. Böbel, M. Chaves, J.-L. Gouzé, "Circadian Clock Model with Sequestration Repression Motif: Existence of Periodic Orbits and Entrainment Properties", *Interface Focus* 15(3) (2025), 20250008, Section 2, Assumption 3.1, Theorems 3.5 and 3.7, Corollary 3.8 and Lemmas 7.1–7.2, <https://doi.org/10.1098/rsfs.2025.0008> (preprint arXiv:2506.03649).
