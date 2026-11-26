# Thermal trace token

A token of the trace format as written, $[-]n/d$, consists of three fields:

- a flag saying whether it starts with $\texttt{'-'}$;
- the numerator digit characters, most significant first;
- the denominator digit characters, most significant first.

Leading zeros are part of the token. The two character lists are unrestricted: they may be empty or contain characters other than decimal digits. Only an [admissible](admissible.md) token has validated digit runs of one to eleven decimal digits and bounded numerator and denominator.
