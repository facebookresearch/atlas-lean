# The hire-assistant scan

Given candidates $x_0, \dots, x_{n-1}$ in a linearly ordered type,
the scan interviews them in order while keeping a current manager, initially none, which counts
as below every candidate. Candidate $i$ is hired exactly when $x_i$ is strictly greater than the
value of the current manager, and then becomes the new manager; ties keep the earlier manager.
The scan returns the zero-based index of the final manager (none for the empty list) and the
list of hired indices in the order they were hired, and its cost is the pair (number of
interviews, number of hires).
