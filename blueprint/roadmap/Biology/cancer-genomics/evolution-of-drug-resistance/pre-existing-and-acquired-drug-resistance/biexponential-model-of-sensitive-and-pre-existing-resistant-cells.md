# Biexponential model of sensitive and pre-existing resistant cells

**Model.** At the start of a constant-effect treatment ($t = 0$) a tumour contains sensitive cells of total size $a > 0$ and resistant cells of total size $c \ge 0$. Assume each subpopulation grows deterministically and exponentially and independently of the other, the sensitive cells at net rate $b < 0$ and the resistant cells at net rate $d > 0$. Then the total size is

$$V(t) = a\,e^{bt} + c\,e^{dt}, \qquad t \ge 0,$$

and a treatment against which no resistant cells pre-exist corresponds to $c = 0$, $V(t) = a e^{bt}$.

**Nadir and relapse.** $V$ is strictly convex. If $0 < c\,d < a\,|b|$ (resistant cells are present and the tumour initially shrinks), $V$ has a unique minimum at

$$t^* = \frac{1}{d-b}\,\ln\!\frac{a\,|b|}{c\,d} > 0,$$

after which it grows and is asymptotic to $c\,e^{dt}$; if $c = 0$, $V = a e^{bt}$ decreases to $0$ with no relapse; if $c\,d \ge a\,|b|$, $V$ is increasing from the start. The initial resistant fraction $c/(a+c)$ and the rates $b, d$ are identifiable from a time course of $V$ that contains both the decline and the regrowth.

## Expansion

$V'(t) = ab\,e^{bt} + cd\,e^{dt}$ and $V''(t) = ab^2 e^{bt} + cd^2 e^{dt} > 0$. Setting $V'(t) = 0$ gives $e^{(d-b)t} = a|b|/(cd)$, which has a positive root exactly when $a|b| > cd$. Fitted to patient-derived colorectal xenografts under anti-EGFR antibody, the model put about 2% of the initial tumour volume in a resistant compartment growing at about $0.04$ per day while sensitive cells declined at about $0.06$ per day; under combined EGFR and MEK blockade a single declining compartment ($c = 0$) fitted the data. The model assumes exponential growth, which fails for large tumours where growth becomes logistic.

## Sources

- S. Misale, I. Bozic, J. Tong et al., "Vertical suppression of the EGFR pathway prevents onset of resistance in colorectal cancers", Nature Communications 6 (2015) 8305, Results ("Mathematical modelling of drug resistance in PDX" and "Mathematical modelling of drug resistance in cell models", Eq. (1)), <https://doi.org/10.1038/ncomms9305>.
