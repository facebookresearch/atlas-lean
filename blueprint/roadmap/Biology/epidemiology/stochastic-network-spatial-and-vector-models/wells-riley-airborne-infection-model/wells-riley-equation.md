# Wells–Riley equation

Consider a well-mixed room with steady ventilation (outdoor-air supply) rate $Q > 0$, containing
$I \ge 0$ infectors who each emit infectious quanta at rate $q > 0$, and susceptibles who breathe
at pulmonary ventilation rate $p > 0$ for an exposure time $t > 0$. A quantum is the dose that
infects a susceptible with probability $1 - e^{-1}$, so the number of quanta inhaled is Poisson
with mean equal to the inhaled dose. At steady state the quanta concentration is $Iq/Q$, the mean
dose is $Iqpt/Q$, and the probability that a susceptible is infected is

$$P = 1 - \exp\!\left(-\frac{I q p t}{Q}\right).$$

Equivalently, the expected number of new cases among $S$ susceptibles is $SP$. For a target
infection probability $P^\ast \in (0,1)$, the ventilation rate must satisfy

$$Q \ \ge\ \frac{I q p t}{-\ln(1 - P^\ast)} .$$

## Expansion

In a well-mixed space the quanta concentration $C$ obeys $V\dot C = Iq - QC$ for room volume $V$,
which relaxes to $C = Iq/Q$ on the time scale $V/Q$; the equation assumes exposure is long
compared with that time scale and neglects other removal (deposition, inactivation, filtration),
which can be added to $Q$ as equivalent ventilation. Inhalation is a Poisson process of quanta
with mean $Cpt$, so the probability of at least one is $1 - e^{-Cpt}$. Solving $P \le P^\ast$ for
$Q$ gives the ventilation bound, which is linear in the emission rate $q$ and the exposure time
$t$. In the source, $q$ for an infector is fitted so that the Wells–Riley case count matches a
reproduction number, and the bound is used to show that common ventilation rates are too low to
keep $P$ below 1% over long exposures.

## Sources

- H. Dai, B. Zhao, "Association of the infection probability of COVID-19 with ventilation rates in
  confined spaces", Building Simulation 13 (2020), abstract (Wells–Riley equation with a fitted
  quantum generation rate), <https://doi.org/10.1007/s12273-020-0703-5> (PMC7398856).
- E. C. Riley, G. Murphy, R. L. Riley, "Airborne spread of measles in a suburban elementary
  school", American Journal of Epidemiology 107 (1978) 421-432 (original form of the equation).
