# Graham's list scheduling

Given $m \ge 1$ identical machines and a list of job
processing times (natural numbers), start with every machine empty and take the jobs in the
given order, appending each job to the list of a currently least-loaded machine (the first one in
index order), where the load of a machine is the sum of its jobs. The result assigns to each
machine its list of jobs. The cost counted is $m$ per job, one unit for each machine load
inspected.
