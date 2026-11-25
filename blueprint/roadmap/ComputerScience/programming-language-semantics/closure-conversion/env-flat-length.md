# Length of an evaluated flat environment

Let $\mathrm{acc}$ be a map from natural numbers
to target terms and $i_1, \dots, i_n$ a list of natural numbers. If the flat environment
$(\mathrm{acc}(i_1), (\dots, (\mathrm{acc}(i_n), \mathsf{unit})\dots))$ evaluates in some target
environment to the encoding $(w_1, (\dots, (w_k, \mathsf{unit})\dots))$ of a list of target values
$w_1, \dots, w_k$, then $k = n$.
