# Article Run

A safety abstraction of Figure 6 runs for a single consensus instance. The same failure
pattern and trace witness a detector in the eventually strong class ◇S (strong completeness and
eventual weak accuracy), a history permitted by that detector, a strict correct majority, local
proposals by every correct process, eventual receipt of ordinary sends to correct destinations,
and reliable broadcast of the projected decision requests. A recipient need not have proposed
when a request is delivered. Each correct process is the actor
at arbitrarily late ticks. An unrestricted `wait p` counts, even at an enabled instruction;
this scheduling condition does not enforce local instruction progress or imply termination.
