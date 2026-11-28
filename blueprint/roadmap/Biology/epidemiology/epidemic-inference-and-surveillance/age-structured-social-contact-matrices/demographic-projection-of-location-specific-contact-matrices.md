# Demographic projection of location-specific contact matrices

Let $\lambda^L_{a,\alpha}$ ($L \in \{H, W, S, O\}$) be location-specific contact rates estimated in a set of reference countries with contact-survey data, let $P^{\mathrm{ref}}_\alpha$ be the proportion of the pooled reference population in age group $\alpha$, and let $P^c_a$ be the proportion of the population of a target country $c$ in age group $a$. The location-specific contact matrices of $c$ are projected as follows.

**Home.** Let $h^c_{a,\alpha}$ (the household age matrix) be the mean number of household members of age $\alpha$ of an individual aged $a$, and define the population ratio matrix

$$\Pi^c_{a,\alpha} = \frac{h^c_{a,\alpha}}{P^c_a}. \tag{2}$$

For a country without household data, $h^c$ is projected from a weighted mean of the matrices $\Pi$ of countries with household data, the weights coming from distances between standardized socio-demographic indicators. Then

$$\mu^{H,c}_{a,\alpha} = \lambda^H_{a,\alpha}\, h^c_{a,\alpha}. \tag{3}$$

**Work.** With $w^c_a$ the labour-force participation rate of age group $a$, set $W^c_{a,\alpha} = w^c_a w^c_\alpha$ and

$$\mu^{W,c}_{a,\alpha} = \lambda^W_{a,\alpha}\, W^c_{a,\alpha}\, \frac{P^c_\alpha}{P^{\mathrm{ref}}_\alpha}. \tag{4}$$

**School.** With enrolment rates $e^c_a$, the students of age $a$ are $s^c_a = P^c_a e^c_a$; the number of teachers is $n^c_t = C^c \sum_a s^c_a$ with $C^c$ the factor derived from the pupil–teacher ratio (Eq. 5), and the teachers of age $a$ are $t^c_a = P^c_a\, n^c_t\, w^c_a$ (Eq. 6). The school mixing matrix is

$$S^c_{a,\alpha} = \left(\frac{s^c_a}{\sum_i s^c_i} + \frac{t^c_a}{\sum_i t^c_i}\right)\left(\frac{s^c_\alpha}{\sum_i s^c_i} + \frac{t^c_\alpha}{\sum_i t^c_i}\right), \tag{7}$$

and

$$\mu^{S,c}_{a,\alpha} = \lambda^S_{a,\alpha}\, \frac{P^c_\alpha}{P^{\mathrm{ref}}_\alpha}\, S^c_{a,\alpha}. \tag{8}$$

**Other locations.**

$$\mu^{O,c}_{a,\alpha} = \lambda^O_{a,\alpha}\, \frac{P^c_\alpha}{P^{\mathrm{ref}}_\alpha}. \tag{9}$$

The all-location matrix is $\mu^c = \mu^{H,c} + \mu^{W,c} + \mu^{S,c} + \mu^{O,c}$.

Properties:

- $W^c$ and $S^c$ are symmetric rank-one matrices (outer products of a vector with itself), so all age structure of work and school mixing beyond the reference rates enters through one age profile each;
- if $c$ has the reference age distribution ($P^c = P^{\mathrm{ref}}$), then $\mu^{O,c} = \lambda^O$: the other-location projection only reweights contacts by the relative abundance of contactable ages;
- an exact household age matrix satisfies the reciprocity identity $P^c_a\, h^c_{a,\alpha} = P^c_\alpha\, h^c_{\alpha,a}$, because both sides count, per head of total population, the ordered cohabiting pairs (individual of age $a$, cohabitant of age $\alpha$) from either end; summing over $\alpha$ gives $\sum_\alpha P^c_\alpha h^c_{\alpha,a} = P^c_a \sum_\alpha h^c_{a,\alpha}$, which is proportional to $P^c_a$ whenever the mean number of cohabitants does not depend on age. The projection uses this proportionality to select among bootstrap weightings.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The construction keeps the age-and-location contact propensities $\lambda^L$ learned from survey countries and replaces only the demographic ingredients (household composition, workforce, school population, age pyramid) by those of the target country. Leave-one-out reconstruction of empirical household age matrices gave a median correlation of 0.93, and the projected matrices were checked against independent contact surveys in five low- and middle-income countries. Scaled to a target basic reproduction number through the dominant eigenvalue of the [next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md), the matrices drive an age-structured SIR model in which the benefit of school closure or workplace distancing depends on the country's age structure.

## Sources

- K. Prem, A. R. Cook, M. Jit, "Projecting social contact matrices in 152 countries using contact surveys and demographic data", PLoS Computational Biology 13(9) (2017) e1005697, Materials and methods, "Extension to the non-POLYMOD countries", "Age-specific contacts in the workplace", "Age-specific contacts in school", "Age-specific contacts at other locations", Eqs. (2)–(9), and "Validation", <https://doi.org/10.1371/journal.pcbi.1005697> (PMC5609774).
