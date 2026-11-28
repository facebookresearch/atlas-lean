# Late eq of map eq

A binary-instrument potential-outcomes model on a measurable space $\Omega$ consists of a measurable instrument $Z : \Omega \to \{0,1\}$, measurable potential treatments $D(z) : \Omega \to \{0,1\}$ and measurable potential outcomes $Y(z,d) : \Omega \to \mathbb R$ for $z, d \in \{0,1\}$; the observed treatment is $D = D(Z)$ and the observed outcome is $Y = Y(Z, D(Z))$. The compliers are the units with $D(0) = 0$ and $D(1) = 1$.

Let two such models be given on probability spaces $(\Omega, \mu)$ and $(\Omega', \mu')$, and assume for each of them:

- independence: $Z$ is independent of the vector $\bigl((D(z))_z, (Y(z,d))_{z,d}\bigr)$ of all potential treatments and outcomes;
- exclusion: $Y(0, d) = Y(1, d)$ everywhere, for both $d$;
- monotonicity: $D(0) \le D(1)$ everywhere;
- every $Y(z,d)$ is integrable;
- $\mu(Z = z) \ne 0$ for both $z$;
- the compliers have nonzero measure.

If the observed triples $(Z, D, Y)$ and $(Z', D', Y')$ have the same law, then for all $z, z' \in \{0,1\}$ the complier average effects agree:

$$\mathbb E_\mu\bigl[Y(z,1) - Y(z,0) \mid \text{complier}\bigr] = \mathbb E_{\mu'}\bigl[Y'(z',1) - Y'(z',0) \mid \text{complier}'\bigr],$$

the expectations being taken under the measures conditioned on the complier sets. Thus the complier average effect is identified from the joint law of $(Y, D, Z)$ (Imbens & Angrist 1994, Theorem 1, with joint random assignment as the independence condition).
