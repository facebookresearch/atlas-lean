# Bayesian consistency of the ACMG/AMP combining rules

**Setting.** Use the [exponentially scaled odds of pathogenicity](exponentially-scaled-odds-of-pathogenicity.md) model with $X = 2$, $O_{\mathrm{VSt}} = 350$ and prior $P_0 = 0.10$. Each qualitative ACMG/AMP combining rule (a count of evidence items at each strength) then has a combined odds $O_P = 350^{e}$ and a posterior $\mathrm{Post}_P = O_P P_0/((O_P-1)P_0+1)$. For the pathogenic and likely-pathogenic rules, which use pathogenic evidence only, $e = N_{\mathrm{Su}}/8 + N_{\mathrm M}/4 + N_{\mathrm{St}}/2 + N_{\mathrm{VSt}}$. For the benign and likely-benign rules, which use benign evidence only, the exponent is negative, $e = -N_{\mathrm{BSu}}/8 - N_{\mathrm{BSt}}/2$ with $N_{\mathrm{BSu}}, N_{\mathrm{BSt}}$ the numbers of benign supporting and benign strong items (the source's equation 2, "OP = O_PVSt^(−N_BSu/X³ − N_BSt/X)"). The stand-alone benign criterion BA1 is excluded from the model. A rule is consistent if its posterior falls in the band of the class it assigns: $>0.99$ pathogenic, $[0.900, 0.99]$ likely pathogenic, $[0.001, 0.10)$ likely benign and $<0.001$ benign (the source: "the Post_Ps of the likely benign combinations would be between 0.001 and <0.10" and "the one benign category has Post_P <0.001").

**Proposition.** Under this calibration:

- The ACMG/AMP *pathogenic* rule "two strong items" has $e = 1$, $O_P = 350$ and

$$\mathrm{Post}_P = \frac{35}{35.9} \approx 0.975,$$

so it reaches only the likely-pathogenic band.
- The *likely pathogenic* rule "one very strong and one moderate item" has $e = 5/4$, $O_P = 350^{5/4} \approx 1514$ and $\mathrm{Post}_P \approx 0.994$, so it reaches the pathogenic band.
- The likely-pathogenic rules "one strong and one moderate", "one strong and two supporting", "three moderate", "two moderate and two supporting" and "one moderate and four supporting" all have $e = 3/4$ and $\mathrm{Post}_P \approx 0.90$, at the lower edge of their band; the remaining pathogenic rules (for example one very strong plus one strong, $e = 3/2$) give $\mathrm{Post}_P \ge 0.994$.
- The benign rule "two benign strong items" has $e = -1$ and $\mathrm{Post}_P \approx 3.2 \times 10^{-4} < 0.001$. The likely-benign rules "one benign strong and one benign supporting item" ($e = -5/8$, $\mathrm{Post}_P \approx 0.0028$) and "two benign supporting items" ($e = -1/4$, $O_P = 350^{-1/4} \approx 0.23$, $\mathrm{Post}_P \approx 0.025$) fall in $[0.001, 0.10)$. All three are consistent.

Thus, of the 18 ACMG/AMP combining rules, BA1 is a stand-alone criterion outside the model, and of the remaining 17 only these two (pathogenic rule (ii) and likely pathogenic rule (i)) are inconsistent with the Bayesian framework; the paper found $X = 2$ to be the uniquely best exponent and other $(O_{\mathrm{VSt}}, P_0)$ pairs in the same region to give the same conclusions. (The five rules (ii)–(vi) with $e = 3/4$ give $350^{3/4} \approx 80.92$ and $\mathrm{Post}_P \approx 0.8999$, which count as consistent after rounding to three decimals ($0.900 \in [0.900, 0.99]$) as in the source.)

## Depends on

- [Exponentially scaled odds of pathogenicity](exponentially-scaled-odds-of-pathogenicity.md)

## Expansion

Every combination is a sum of the exponents $1/8, 1/4, 1/2, 1$, so the classification reduces to comparing $e$ with the exponents at which $\mathrm{Post}_P$ crosses $0.90$ and $0.99$. With $P_0 = 0.1$ the prior odds are $1/9$, so $\mathrm{Post}_P > 0.99$ needs $O_P > 891$, i.e. $e > \ln 891/\ln 350 \approx 1.16$, and $\mathrm{Post}_P > 0.90$ needs $O_P > 81$, i.e. $e > \ln 81/\ln 350 \approx 0.750$. Two strong items give $e = 1 < 1.16$ (not pathogenic), while very strong plus moderate gives $e = 1.25 > 1.16$ (pathogenic). The same arithmetic scores mixed pathogenic-plus-benign combinations, which the qualitative guidelines leave as uncertain significance, as likely pathogenic, likely benign or uncertain depending on the net exponent.

## Sources

- S. V. Tavtigian, M. S. Greenblatt, S. M. Harrison et al., "Modeling the ACMG/AMP variant classification guidelines as a Bayesian classification framework", Genetics in Medicine (2018), Results and Table 1, <https://doi.org/10.1038/gim.2017.210> (PMC6336098).
