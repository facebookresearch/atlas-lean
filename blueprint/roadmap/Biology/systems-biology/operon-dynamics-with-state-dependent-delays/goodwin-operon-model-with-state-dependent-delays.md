# Goodwin operon model with state-dependent transcription and translation delays

Let $M(t)$, $I(t)$, $E(t)$ be the concentrations of mRNA, intermediate protein and effector in a cell growing exponentially at rate $\mu\ge0$, and let $\bar\gamma_X=\gamma_X+\mu$ be the degradation rates augmented by dilution. Let $v_M(E)>0$ be the transcription velocity, $v_I(M)>0$ the translation velocity, and $a_M,a_I>0$ the lengths of the transcribed and translated regions. The delays $\tau_M(t),\tau_I(t)$ are defined implicitly by the threshold conditions

$$a_M=\int_{t-\tau_M(t)}^{t}v_M\big(E(s)\big)\,ds,\qquad a_I=\int_{t-\tau_I(t)}^{t}v_I\big(M(s)\big)\,ds,$$

and the dynamics are

$$\frac{dM}{dt}=\beta_Me^{-\mu\tau_M(t)}\frac{v_M(E(t))}{v_M(E(t-\tau_M(t)))}f\big(E(t-\tau_M(t))\big)-\bar\gamma_MM(t),$$

$$\frac{dI}{dt}=\beta_Ie^{-\mu\tau_I(t)}\frac{v_I(M(t))}{v_I(M(t-\tau_I(t)))}M\big(t-\tau_I(t)\big)-\bar\gamma_II(t),\qquad \frac{dE}{dt}=\beta_EI(t)-\bar\gamma_EE(t).$$

Here $\beta_M$ is the maximal transcription initiation flux and $f$ is the fraction of free operator sites: $f(E)=\frac{1+K_1E^n}{1+KE^n}$ with $K>K_1$ for a repressible operon and $f(E)=\frac{1+K_1E^n}{K+K_1E^n}$ with $K>1$ for an inducible operon ($n>1$). If $0<v^{\min}\le v\le v^{\max}$, the delays satisfy $a/v^{\max}\le\tau\le a/v^{\min}$. With constant velocities $v_M,v_I$ the threshold conditions give the constant delays $\tau_M=a_M/v_M$ and $\tau_I=a_I/v_I$ and the velocity ratios equal $1$; if moreover $\mu=0$, so that $\bar\gamma_X=\gamma_X$, the system becomes the constant-delay Goodwin model

$$\dot M(t)=\beta_Mf\big(E(t-\tau_M)\big)-\gamma_MM(t),\qquad \dot I(t)=\beta_IM(t-\tau_I)-\gamma_II(t),\qquad \dot E(t)=\beta_EI(t)-\gamma_EE(t),$$

in which the first two inputs still lag by $\tau_M,\tau_I>0$. Only after further setting both delays to zero does it become the classical instantaneous Goodwin model $\dot M=F(E)-\gamma_MM$, $\dot I=\beta_IM-\gamma_II$, $\dot E=\beta_EI-\gamma_EE$ with $F=\beta_Mf$.

## Expansion

Model transcripts by a density $r(t,a)$ transported along the gene at speed $v_M(E(t))$: $\partial_tr+v_M\partial_ar=0$. The release rate of completed transcripts is $v_M(E(t))\,r(t,a_M)$, and by characteristics $r(t,a_M)=r(t-\tau_M,0)$, where the delay is the time to traverse length $a_M$. Writing the release rate as $\frac{v_M(E(t))}{v_M(E(t-\tau_M))}$ times the initiation flux $v_M r(t-\tau_M,0)$ at the earlier time produces the velocity ratio. Converting molecule numbers to concentrations in a volume growing as $V(t)=e^{\mu\tau}V(t-\tau)$ produces the dilution factor $e^{-\mu\tau}$ and the extra decay $\mu$. Translation is treated the same way with $v_I(M)$.

## Sources

- T. Gedeon, A. R. Humphries, M. C. Mackey, H.-O. Walther, Z. Wang, "Operon dynamics with state dependent transcription and/or translation delays", J. Math. Biol. 84 (2022), article 2, Sections 2.1–2.5, Equations (2.1)–(2.22) and Table 1, <https://doi.org/10.1007/s00285-021-01693-0>.
