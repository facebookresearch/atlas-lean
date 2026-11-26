# Stability of a resident homing drive against resistant alleles

In the multiallelic model of a CRISPR drive with $n$ guide RNAs, the locus carries the drive $D$, the wild type $S_0 = W$, cost-free partially or fully resistant alleles $S_1, \dots, S_n$ and costly resistant alleles $R_1, \dots, R_n$ (the index counts the destroyed target sites; only $S_n$ and $R_n$ are fully resistant). Genotype $AB$ has viability $f_{AB} > 0$ and produces allele $C$ with probability $p_{AB,C}$; fully resistant heterozygotes segregate normally, $p_{DS_n,S_n} = p_{DR_n,R_n} = \tfrac12$. Dynamics are the deterministic random-mating gamete-production model of Noble et al.

**Theorem (evolutionary stability).** The resident equilibrium in which every individual is $DD$ is stable against invasion by every non-drive allele if and only if

$$\max_{A \in \{S_0, \dots, S_n, R_1, \dots, R_n\}} 2\, p_{DA,A}\, f_{DA} < f_{DD}.$$

**Corollary (instability with cost-free full resistance).** If the fully resistant cost-free allele $S_n$ is produced at a positive rate and $f_{DS_n} \ge f_{DD}$ (for example, when the drive is costly and $S_n$ is functionally wild type, so that $f_{DS_n} = f_{DW} > f_{DD}$), then $2 p_{DS_n,S_n} f_{DS_n} = f_{DS_n} \ge f_{DD}$ and the drive cannot be evolutionarily stable: such an allele invades whenever the strict inequality holds.

## Depends on

- [Invasion condition for a homing gene drive](invasion-condition-for-a-homing-gene-drive.md)

## Expansion

Near the all-$DD$ state, $F_D = f_{DD} + O(\varepsilon)$, $\psi = f_{DD} + O(\varepsilon)$, and each non-drive allele $A$ occurs to first order only in $DA$ heterozygotes, with $\dot x_{DA} = 2 F_A F_D - \psi^2 x_{DA}$. A $DA$ individual produces $A$ gametes at rate $p_{DA,A} f_{DA}$ and, through misrepair, gametes of alleles with more destroyed target sites. Ordering the non-drive alleles by the number of destroyed sites (and $S_k$ before $R_k$), the linearized system is triangular, so its eigenvalues are the diagonal rates $\big(2\, p_{DA,A} f_{DA} - f_{DD}\big) f_{DD}$; the resident drive is stable iff all are negative, which is the stated maximum condition, each term having the form of the [invasion condition](invasion-condition-for-a-homing-gene-drive.md) with resident and invader exchanged. For susceptible alleles, homing makes $p_{DA,A}$ small, which suppresses invasion. The corollary explains why single-guide constructs that disrupt the target gene are unstable: in-frame repair produces a functional cut-resistant allele that transmits normally against the drive. The proposed remedy targets several sites in an essential gene and carries a recoded rescue copy, so most repair events yield costly $R$ alleles with low $f_{DR}$; numerically such drives with five guides stay above $99\%$ frequency for at least 200 generations over drive costs up to about $30\%$.

## Sources

- C. Noble, J. Olejarz, K. M. Esvelt, G. M. Church and M. A. Nowak, "Evolutionary dynamics of CRISPR gene drives", Science Advances 3 (2017), e1601964, Results Eq. (2) and the discussion following it (derivation in Supplementary sections S4 and S7.2), <https://doi.org/10.1126/sciadv.1601964>, PMCID PMC5381957.
