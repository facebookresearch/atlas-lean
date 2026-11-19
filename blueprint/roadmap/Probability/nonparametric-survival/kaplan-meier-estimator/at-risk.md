# Number at risk at an observation time

For [grouped right-censored data](censored-data.md), the number at risk at $t_j$ is $n_j = \sum_{l \ge j} (d_l + c_l)$, the number of subjects whose observation time is at least $t_j$.

## Related topics

- [Number at risk in competing-risks data](../competing-risks/at-risk.md): the same count for competing-risks data, with the failures from all causes pooled.
