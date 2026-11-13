# Running an edit script

Over a type $\alpha$ with a boolean equality test, running an
edit script on an input list processes the steps from left to right and either fails or
returns an output list. A keep step with value $a$ consumes the next input value $b$ and
outputs $a$; a deletion of $a$ consumes $b$ and outputs nothing; a substitution of $a$ by $c$
consumes $b$ and outputs $c$. Each of these three fails if the input is exhausted or if the
equality test of $a$ against $b$ fails. An insertion of $c$ outputs $c$ without consuming input.
When the script ends, the run succeeds with the outputs in order if the input is used up, and
fails if input values remain.
