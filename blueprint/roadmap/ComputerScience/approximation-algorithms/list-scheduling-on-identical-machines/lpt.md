# Longest processing time first (LPT)

Given $m \ge 1$ identical machines and a list of job
processing times (natural numbers), LPT sorts the jobs into nonincreasing order by merge sort and
then applies Graham's list scheduling on $m$ machines to the sorted list. The cost counted is the
number of comparisons made by merge sort plus the cost of list scheduling, $m$ per job.
