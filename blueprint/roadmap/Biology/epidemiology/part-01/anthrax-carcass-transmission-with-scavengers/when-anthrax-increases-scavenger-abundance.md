# When anthrax increases scavenger abundance

**Setting.** In the [zebra–carcass–scavenger anthrax model](equilibria-and-thresholds-of-the-zebra-carcass-scavenger-anthrax-model.md) let $m = \mu/r$ (zebra death-to-birth ratio), $\varphi = ad/(br)$ (a scavenger death-to-birth ratio) and $p = \rho/(aK)$ (carcass decay relative to spore-source creation). Let $j_2^*$ and $j_4^*$ be the scavenger abundances at the anthrax-free equilibrium $E_2$ and the coexistence equilibrium $E_4$, and $D(E_1)$, $D(E_3)$ the scavenger demographic reproduction numbers without and with anthrax.

**Theorem 1.** $\ j_4^* > j_2^*$ if and only if $\varphi$ lies strictly between $m$ and $1-m$.

**Theorem 2.** $\ D(E_3) > D(E_1)$ if and only if $p$ lies strictly between $m$ and $1-m$.

Thus anthrax raises the scavengers' reproduction number exactly when $p$ is closer to $1/2$ than $m$ is, and raises their equilibrium abundance exactly when $\varphi$ is closer to $1/2$ than $m$ is.

## Expansion

From the equilibrium formulas, $j_4^* > j_2^* \iff \frac{aK}{\alpha}(1-\varphi) - \frac{\rho}{\alpha} > \frac{b\mu}{\alpha d}K(1-m) - \frac{\rho}{\alpha}$, which simplifies to $\varphi(1-\varphi) > m(1-m)$, i.e. $(\varphi - m)(\varphi + m - 1) < 0$. Likewise $D(E_3) > D(E_1) \iff \frac{br}{ad}(1-p) > \frac{b\mu}{\rho d}K(1-m)$, which reduces to $p(1-p) > m(1-m)$. Since $x \mapsto x(1-x)$ is symmetric about $1/2$, the condition says the ratio is less extreme than $m$. Anthrax both feeds scavengers through extra carcasses and depresses the zebra population that produces natural carcasses; the inequalities record which effect wins.

## Depends on

- [Equilibria and thresholds of the zebra–carcass–scavenger anthrax model](equilibria-and-thresholds-of-the-zebra-carcass-scavenger-anthrax-model.md)

## Sources

- Mackey C, Kribs C, "Can scavengers save zebras from anthrax? A modeling study", Infect Dis Model (2021), Section 4, Theorems 1–2, <https://doi.org/10.1016/j.idm.2020.10.016>, PMCID PMC7708949.
